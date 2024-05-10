const std = @import("std");

const MicrokitBoard = enum { qemu_arm_virt, odroidc4, maaxboard };

const Target = struct {
    board: MicrokitBoard,
    zig_target: std.zig.CrossTarget,
};

const targets = [_]Target{
    .{
        .board = MicrokitBoard.qemu_arm_virt,
        .zig_target = std.zig.CrossTarget{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.arm.cpu.cortex_a53 },
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.odroidc4,
        .zig_target = std.zig.CrossTarget{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.arm.cpu.cortex_a55 },
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.maaxboard,
        .zig_target = std.zig.CrossTarget{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.arm.cpu.cortex_a53 },
            .os_tag = .freestanding,
            .abi = .none,
        },
    }
};

fn findTarget(board: MicrokitBoard) std.zig.CrossTarget {
    for (targets) |target| {
        if (board == target.board) {
            return target.zig_target;
        }
    }

    std.log.err("Board '{}' is not supported\n", .{board});
    std.posix.exit(1);
}

const ConfigOptions = enum { debug, release, benchmark };

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});

    // Getting the path to the Microkit SDK before doing anything else
    const microkit_sdk_arg = b.option([]const u8, "sdk", "Path to Microkit SDK");
    if (microkit_sdk_arg == null) {
        std.log.err("Missing -Dsdk=/path/to/sdk argument being passed\n", .{});
        std.posix.exit(1);
    }
    const microkit_sdk = microkit_sdk_arg.?;

    const microkit_config_option = b.option(ConfigOptions, "config", "Microkit config to build for") orelse ConfigOptions.debug;
    const microkit_config = @tagName(microkit_config_option);

    // Get the Microkit SDK board we want to target
    const microkit_board_option = b.option(MicrokitBoard, "board", "Microkit board to target");

    if (microkit_board_option == null) {
        std.log.err("Missing -Dboard=<BOARD> argument being passed\n", .{});
        std.posix.exit(1);
    }
    const target = b.resolveTargetQuery(findTarget(microkit_board_option.?));
    const microkit_board = @tagName(microkit_board_option.?);

    // Since we are relying on Zig to produce the final ELF, it needs to do the
    // linking step as well.
    const microkit_board_dir = b.fmt("{s}/board/{s}/{s}", .{ microkit_sdk, microkit_board, microkit_config });
    const microkit_tool = b.fmt("{s}/bin/microkit", .{microkit_sdk});
    const libmicrokit = b.fmt("{s}/lib/libmicrokit.a", .{microkit_board_dir});
    const libmicrokit_linker_script = b.fmt("{s}/lib/microkit.ld", .{microkit_board_dir});
    const libmicrokit_include = b.fmt("{s}/include", .{microkit_board_dir});

    const sddf_dep = b.dependency("sddf", .{
        .target = target,
        .optimize = optimize,
        .sdk = microkit_sdk,
        .config = @as([]const u8, microkit_config),
        .board = @as([]const u8, microkit_board),
    });
    
    const driver_class = switch (microkit_board_option.?) {
        .qemu_arm_virt => "arm",
        .odroidc4 => "meson",
        .maaxboard => "imx",
    };

    const driver = sddf_dep.artifact(b.fmt("driver_uart_{s}.elf", .{ driver_class }));
    b.installArtifact(driver);

    const virt_rx = sddf_dep.artifact("serial_component_virt_rx.elf");
    b.installArtifact(virt_rx);

    const virt_tx = sddf_dep.artifact("serial_component_virt_tx.elf");
    b.installArtifact(virt_tx);

    const serial_server_1 = b.addExecutable(.{
        .name = "serial_server_1.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });

    serial_server_1.addCSourceFile(.{ .file = b.path("serial_server.c"), .flags = &.{ "-DSERIAL_SERVER_NUMBER=1", "-fno-sanitize=undefined" } });
    serial_server_1.addIncludePath(.{ .path = libmicrokit_include });
    serial_server_1.addIncludePath(sddf_dep.path("include"));
    serial_server_1.addObjectFile(.{ .path = libmicrokit });
    serial_server_1.setLinkerScriptPath(.{ .path = libmicrokit_linker_script });

    const serial_server_2 = b.addExecutable(.{
        .name = "serial_server_2.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });

    serial_server_2.addCSourceFile(.{ .file = b.path("serial_server.c"), .flags = &.{ "-DSERIAL_SERVER_NUMBER=2", "-fno-sanitize=undefined" } });
    serial_server_2.addIncludePath(.{ .path = libmicrokit_include });
    serial_server_2.addIncludePath(sddf_dep.path("include"));
    serial_server_2.addObjectFile(.{ .path = libmicrokit });
    serial_server_2.setLinkerScriptPath(.{ .path = libmicrokit_linker_script });

    b.installArtifact(serial_server_1);
    b.installArtifact(serial_server_2);

    const system_description_path = b.fmt("board/{s}/serial.system", .{microkit_board});
    const final_image_dest = b.getInstallPath(.bin, "./loader.img");
    const microkit_tool_cmd = b.addSystemCommand(&[_][]const u8{
        microkit_tool,
        system_description_path,
        "--search-path", b.getInstallPath(.bin, ""),
        "--board", microkit_board,
        "--config", microkit_config,
        "-o", final_image_dest,
        "-r", b.getInstallPath(.prefix, "./report.txt")
    });
    microkit_tool_cmd.step.dependOn(b.getInstallStep());
    // Add the "microkit" step, and make it the default step when we execute `zig build`>
    const microkit_step = b.step("microkit", "Compile and build the final bootable image");
    microkit_step.dependOn(&microkit_tool_cmd.step);
    b.default_step = microkit_step;

    // This is setting up a `qemu` command for running the system using QEMU,
    // which we only want to do when we have a board that we can actually simulate.
    const loader_arg = b.fmt("loader,file={s},addr=0x70000000,cpu-num=0", .{final_image_dest});
    if (std.mem.eql(u8, microkit_board, "qemu_arm_virt")) {
        const qemu_cmd = b.addSystemCommand(&[_][]const u8{
            "qemu-system-aarch64",
            "-machine",
            "virt,virtualization=on,highmem=off,secure=off",
            "-cpu",
            "cortex-a53",
            "-serial",
            "mon:stdio",
            "-device",
            loader_arg,
            "-m",
            "2G",
            "-nographic",
        });
        qemu_cmd.step.dependOn(b.default_step);
        const simulate_step = b.step("qemu", "Simulate the image using QEMU");
        simulate_step.dependOn(&qemu_cmd.step);
    }
}
