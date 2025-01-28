//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");
const Step = std.Build.Step;
const LazyPath = std.Build.LazyPath;

const MicrokitBoard = enum {
    imx8mm_evk,
    imx8mp_evk,
    imx8mq_evk,
    odroidc2,
    odroidc4,
    maaxboard,
    qemu_virt_aarch64,
    qemu_virt_riscv64,
    star64,
};

const Target = struct {
    board: MicrokitBoard,
    zig_target: std.Target.Query,
};

const targets = [_]Target{
    .{
        .board = MicrokitBoard.qemu_virt_aarch64,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{ .strict_align }),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.odroidc2,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{ .strict_align }),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.odroidc4,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a55 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{ .strict_align }),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.maaxboard,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{ .strict_align }),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.imx8mm_evk,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{ .strict_align }),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.imx8mp_evk,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{ .strict_align }),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.imx8mq_evk,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{ .strict_align }),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.star64,
        .zig_target = std.Target.Query{
            .cpu_arch = .riscv64,
            .cpu_model = .{ .explicit = &std.Target.riscv.cpu.baseline_rv64 },
            .os_tag = .freestanding,
            .abi = .none,
        }
    },
    .{
        .board = MicrokitBoard.qemu_virt_riscv64,
        .zig_target = std.Target.Query{
            .cpu_arch = .riscv64,
            .cpu_model = .{ .explicit = &std.Target.riscv.cpu.baseline_rv64 },
            .os_tag = .freestanding,
            .abi = .none,
        }
    },
};

fn findTarget(board: MicrokitBoard) std.Target.Query {
    for (targets) |target| {
        if (board == target.board) {
            return target.zig_target;
        }
    }

    std.log.err("Board '{}' is not supported\n", .{board});
    std.posix.exit(1);
}

const ConfigOptions = enum { debug, release, benchmark };

fn updateSectionObjcopy(b: *std.Build, section: []const u8, data_output: std.Build.LazyPath, data: []const u8, elf: []const u8) *std.Build.Step.Run {
    const run_objcopy = b.addSystemCommand(&[_][]const u8{
        "llvm-objcopy",
    });
    run_objcopy.addArg("--update-section");
    const data_full_path = data_output.join(b.allocator, data) catch @panic("OOM");
    run_objcopy.addPrefixedFileArg(b.fmt("{s}=", .{ section }), data_full_path);
    run_objcopy.addFileArg(.{ .cwd_relative = b.getInstallPath(.bin, elf) });

    // We need the ELFs we talk about to be in the install directory first.
    run_objcopy.step.dependOn(b.getInstallStep());

    return run_objcopy;
}

pub fn build(b: *std.Build) !void {
    const optimize = b.standardOptimizeOption(.{});

    const default_python = if (std.posix.getenv("PYTHON")) |p| p else "python3";
    const python = b.option([]const u8, "python", "Path to Python to use") orelse default_python;

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
    const libmicrokit_include = b.fmt("{s}/include", .{microkit_board_dir});
    const libmicrokit_linker_script = b.fmt("{s}/lib/microkit.ld", .{microkit_board_dir});

    const sddf_dep = b.dependency("sddf", .{
        .target = target,
        .optimize = optimize,
        .libmicrokit = @as([]const u8, libmicrokit),
        .libmicrokit_include = @as([]const u8, libmicrokit_include),
        .libmicrokit_linker_script = @as([]const u8, libmicrokit_linker_script),
    });

    const driver_class = switch (microkit_board_option.?) {
        .qemu_virt_aarch64 => "arm",
        .odroidc2, .odroidc4 => "meson",
        .maaxboard, .imx8mm_evk, .imx8mp_evk, .imx8mq_evk => "imx",
        .star64 => "snps",
        .qemu_virt_riscv64 => "virtio",
    };

    const driver = sddf_dep.artifact(b.fmt("driver_serial_{s}.elf", .{ driver_class }));
    // This is required because the SDF file is expecting a different name to the artifact we
    // are dealing with.
    const driver_install = b.addInstallArtifact(driver, .{ .dest_sub_path = "serial_driver.elf" });

    const virt_rx = sddf_dep.artifact("serial_virt_rx.elf");
    b.installArtifact(virt_rx);

    const virt_tx = sddf_dep.artifact("serial_virt_tx.elf");
    b.installArtifact(virt_tx);

    const client = b.addExecutable(.{
        .name = "client.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const client1_install = b.addInstallArtifact(client, .{ .dest_sub_path = "client0.elf" });
    const client2_install = b.addInstallArtifact(client, .{ .dest_sub_path = "client1.elf" });

    client.addCSourceFile(.{ .file = b.path("client.c") });
    client.addIncludePath(sddf_dep.path("include"));
    client.addIncludePath(sddf_dep.path("include/microkit"));
    client.linkLibrary(sddf_dep.artifact("util"));
    client.linkLibrary(sddf_dep.artifact("util_putchar_serial"));

    client.addIncludePath(.{ .cwd_relative = libmicrokit_include });
    client.addObjectFile(.{ .cwd_relative = libmicrokit });
    client.setLinkerScript(.{ .cwd_relative = libmicrokit_linker_script });

    b.installArtifact(client);

    // For compiling the DTS into a DTB
    const dts = sddf_dep.path(b.fmt("dts/{s}.dts", .{ microkit_board }));
    const dtc_cmd = b.addSystemCommand(&[_][]const u8{
        "dtc", "-q", "-I", "dts", "-O", "dtb"
    });
    dtc_cmd.addFileInput(dts);
    dtc_cmd.addFileArg(dts);
    const dtb = dtc_cmd.captureStdOut();

    // Run the metaprogram to get sDDF configuration binary files and the SDF file.
    const metaprogram = b.path("meta.py");
    const run_metaprogram = b.addSystemCommand(&[_][]const u8{
        python,
    });
    run_metaprogram.addFileArg(metaprogram);
    run_metaprogram.addFileInput(metaprogram);
    run_metaprogram.addPrefixedDirectoryArg("--sddf=", sddf_dep.path(""));
    run_metaprogram.addPrefixedDirectoryArg("--dtb=", dtb);
    const meta_output = run_metaprogram.addPrefixedOutputDirectoryArg("--output=", "meta_output");
    run_metaprogram.addArg("--board");
    run_metaprogram.addArg(microkit_board);
    run_metaprogram.addArg("--sdf");
    run_metaprogram.addArg("serial.system");

    const meta_output_install = b.addInstallDirectory(.{
        .source_dir = meta_output,
        .install_dir = .prefix,
        .install_subdir = "meta_output",
    });

    const client1_objcopy = updateSectionObjcopy(b, ".serial_client_config", meta_output, "serial_client_client0.data", "client0.elf");
    client1_objcopy.step.dependOn(&client1_install.step);
    const client2_objcopy = updateSectionObjcopy(b, ".serial_client_config", meta_output, "serial_client_client1.data", "client1.elf");
    client2_objcopy.step.dependOn(&client2_install.step);
    const driver_resources_objcopy = updateSectionObjcopy(b, ".device_resources", meta_output, "serial_driver_device_resources.data", "serial_driver.elf");
    driver_resources_objcopy.step.dependOn(&driver_install.step);
    const driver_config_objcopy = updateSectionObjcopy(b, ".serial_driver_config", meta_output, "serial_driver_config.data", "serial_driver.elf");
    driver_config_objcopy.step.dependOn(&driver_install.step);
    const virt_rx_objcopy = updateSectionObjcopy(b, ".serial_virt_rx_config", meta_output, "serial_virt_rx.data", "serial_virt_rx.elf");
    const virt_tx_objcopy = updateSectionObjcopy(b, ".serial_virt_tx_config", meta_output, "serial_virt_tx.data", "serial_virt_tx.elf");
    const objcopys = &.{ client1_objcopy, client2_objcopy, virt_rx_objcopy, virt_tx_objcopy, driver_resources_objcopy, driver_config_objcopy };

    const final_image_dest = b.getInstallPath(.bin, "./loader.img");
    const microkit_tool_cmd = b.addSystemCommand(&[_][]const u8{
        microkit_tool,
        b.getInstallPath(.{ .custom = "meta_output" }, "serial.system"),
        "--search-path", b.getInstallPath(.bin, ""),
        "--board", microkit_board,
        "--config", microkit_config,
        "-o", final_image_dest,
        "-r", b.getInstallPath(.prefix, "./report.txt")
    });
    inline for (objcopys) |objcopy| {
        microkit_tool_cmd.step.dependOn(&objcopy.step);
    }
    microkit_tool_cmd.step.dependOn(&meta_output_install.step);
    microkit_tool_cmd.step.dependOn(b.getInstallStep());
    microkit_tool_cmd.setEnvironmentVariable("MICROKIT_SDK", microkit_sdk);
    // Add the "microkit" step, and make it the default step when we execute `zig build`>
    const microkit_step = b.step("microkit", "Compile and build the final bootable image");
    microkit_step.dependOn(&microkit_tool_cmd.step);
    b.default_step = microkit_step;

    // This is setting up a `qemu` command for running the system using QEMU,
    // which we only want to do when we have a board that we can actually simulate.
    var qemu_cmd: ?*Step.Run = null;
    if (microkit_board_option.? == .qemu_virt_aarch64) {
        const loader_arg = b.fmt("loader,file={s},addr=0x70000000,cpu-num=0", .{final_image_dest});
        qemu_cmd = b.addSystemCommand(&[_][]const u8{
            "qemu-system-aarch64",
            "-machine",
            "virt,virtualization=on",
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
    } else if (microkit_board_option.? == .qemu_virt_riscv64) {
        qemu_cmd = b.addSystemCommand(&[_][]const u8{
            "qemu-system-riscv64",
            "-machine",
            "virt",
            "-serial",
            "mon:stdio",
            "-kernel",
            final_image_dest,
            "-m",
            "2G",
            "-global",
            "virtio-mmio.force-legacy=false",
            "-device",
            "virtio-serial-device",
            "-chardev",
            "pty,id=virtcon",
            "-device",
            "virtconsole,chardev=virtcon",
            "-nographic",
        });
    }

    if (qemu_cmd) |cmd| {
        cmd.step.dependOn(b.default_step);
        const simulate_step = b.step("qemu", "Simulate the image using QEMU");
        simulate_step.dependOn(&cmd.step);
    }
}
