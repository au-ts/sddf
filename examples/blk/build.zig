//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");

const MicrokitBoard = enum {
    qemu_virt_aarch64
};

const Target = struct {
    board: MicrokitBoard,
    zig_target: std.Target.Query,
};

const targets = [_]Target{
    .{
        .board = .qemu_virt_aarch64,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.arm.cpu.cortex_a53 },
            .os_tag = .freestanding,
            .abi = .none,
        },
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
        .blk_config_include = @as([]const u8, ""),
    });

    const blk_driver_class = switch (microkit_board_option.?) {
        .qemu_virt_aarch64 => "virtio",
    };

    const client_data_cmd = b.addSystemCommand(&[_][]const u8{
        "xxd", "-n", "basic_data", "-i"
    });
    client_data_cmd.addFileArg(b.path("basic_data.txt"));
    client_data_cmd.addFileInput(b.path("basic_data.txt"));
    const client_data = client_data_cmd.addOutputFileArg("basic_data.h");

    const client = b.addExecutable(.{
        .name = "client.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });

    client.addCSourceFiles(.{
        .files = &.{ "client.c" },
    });
    // For blk_config.h
    client.addIncludePath(b.path(""));

    // For the generated client data
    client.step.dependOn(&client_data_cmd.step);
    client.addIncludePath(client_data.dirname());

    client.addIncludePath(sddf_dep.path("include"));
    client.linkLibrary(sddf_dep.artifact("util"));
    client.linkLibrary(sddf_dep.artifact("util_putchar_debug"));

    client.addIncludePath(.{ .cwd_relative = libmicrokit_include });
    client.addObjectFile(.{ .cwd_relative = libmicrokit });
    client.setLinkerScriptPath(.{ .cwd_relative = libmicrokit_linker_script });

    const blk_driver = sddf_dep.artifact(b.fmt("driver_blk_{s}.elf", .{ blk_driver_class }));

    b.installArtifact(client);
    b.installArtifact(blk_driver);
    b.installArtifact(sddf_dep.artifact("blk_virt.elf"));

    // Because our SDF expects a different ELF name for the block driver, we have this extra step.
    const blk_driver_install = b.addInstallArtifact(blk_driver, .{ .dest_sub_path = "blk_driver.elf" });

    const system_description_path = b.fmt("board/{s}/blk.system", .{microkit_board});
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

    const microkit_step = b.step("microkit", "Compile and build the final bootable image");
    microkit_step.dependOn(&blk_driver_install.step);
    microkit_step.dependOn(&microkit_tool_cmd.step);
    b.default_step = microkit_step;

    // This is setting up a `qemu` command for running the system using QEMU,
    // which we only want to do when we have a board that we can actually simulate.
    const loader_arg = b.fmt("loader,file={s},addr=0x70000000,cpu-num=0", .{ final_image_dest });
    if (std.mem.eql(u8, microkit_board, "qemu_virt_aarch64")) {
        const create_disk_cmd = b.addSystemCommand(&[_][]const u8{
            "bash", "mkvirtdisk",
        });
        const disk = create_disk_cmd.addOutputFileArg("disk");
        create_disk_cmd.addArgs(&[_][]const u8{
            "1", "512", b.fmt("{}", .{ 1024 * 1024 * 16 }),
        });
        const disk_install = b.addInstallFile(disk, "disk");
        disk_install.step.dependOn(&create_disk_cmd.step);

        const qemu_cmd = b.addSystemCommand(&[_][]const u8{
            "qemu-system-aarch64",
            "-machine", "virt,virtualization=on,highmem=off,secure=off",
            "-cpu", "cortex-a53",
            "-serial", "mon:stdio",
            "-device", loader_arg,
            "-m", "2G",
            "-nographic",
            "-global", "virtio-mmio.force-legacy=false",
            "-d", "guest_errors",
            "-drive", b.fmt("file={s},if=none,format=raw,id=hd", .{ b.getInstallPath(.prefix, "disk") }),
            "-device", "virtio-blk-device,drive=hd",
            // "--trace", "events=/tmp/events",
        });
        qemu_cmd.step.dependOn(b.default_step);
        qemu_cmd.step.dependOn(&disk_install.step);
        const simulate_step = b.step("qemu", "Simulate the image using QEMU");
        simulate_step.dependOn(&qemu_cmd.step);
    }
}
