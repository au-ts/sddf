//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");
const LazyPath = std.Build.LazyPath;

const MicrokitBoard = enum { qemu_virt_aarch64, odroidc4, maaxboard, star64 };

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
        .board = MicrokitBoard.star64,
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

pub fn build(b: *std.Build) !void {
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
    const libmicrokit_include = b.fmt("{s}/include", .{microkit_board_dir});
    const libmicrokit_linker_script = b.fmt("{s}/lib/microkit.ld", .{microkit_board_dir});

    const sdfgen_dep = b.dependency("sdfgen", .{
        .target = b.graph.host,
        .optimize = optimize,
    });

    const meta = b.addExecutable(.{
        .name = "meta",
        .root_source_file = b.path("meta.zig"),
        .target = b.graph.host,
        .optimize = .ReleaseSafe,
    });
    meta.root_module.addImport("sdf", sdfgen_dep.module("sdf"));
    const meta_run = b.addRunArtifact(meta);

    const sdf_file = meta_run.captureStdOut();

    const config_data = .{
        .{ "client0.data", "client_config.h", "client0_data" },
        .{ "serial_virt_tx.data", "virt_tx_config.h", "serial_virt_tx_data" },
        .{ "serial_virt_rx.data", "virt_rx_config.h", "serial_virt_rx_data" },
        .{ "serial_driver.data", "driver_config.h", "serial_driver_data" },
    };

    var config_headers = try std.ArrayList(LazyPath).initCapacity(b.allocator, config_data.len);
    defer config_headers.deinit();
    inline for (config_data) |config| {
        const data = b.path(config[0]);
        const data_to_header = b.addSystemCommand(&[_][]const u8{
            "xxd", "-n", config[2], "-i"
        });
        data_to_header.step.dependOn(&meta_run.step);
        data_to_header.addFileArg(data);
        data_to_header.addFileInput(data);
        const header = data_to_header.captureStdOut();

        config_headers.appendAssumeCapacity(header);
    }

    const meta_step = b.step("meta", "Run metaprogram");
    inline for (config_data, 0..) |config, i| {
        meta_step.dependOn(&b.addInstallFileWithDir(config_headers.items[i], .prefix, config[1]).step);
    }
    meta_step.dependOn(&meta_run.step);

    const sddf_dep = b.dependency("sddf", .{
        .target = target,
        .optimize = optimize,
        .libmicrokit = @as([]const u8, libmicrokit),
        .libmicrokit_include = @as([]const u8, libmicrokit_include),
        .libmicrokit_linker_script = @as([]const u8, libmicrokit_linker_script),
        .serial_config_include = b.getInstallPath(.prefix, ""),
    });

    const driver_class = switch (microkit_board_option.?) {
        .qemu_virt_aarch64 => "arm",
        .odroidc4 => "meson",
        .maaxboard => "imx",
        .star64 => "snps",
    };

    const driver = sddf_dep.artifact(b.fmt("driver_uart_{s}.elf", .{ driver_class }));
    // This is required because the SDF file is expecting a different name to the artifact we
    // are dealing with.
    const driver_install = b.addInstallArtifact(driver, .{ .dest_sub_path = "uart_driver.elf" });

    const virt_rx = sddf_dep.artifact("serial_virt_rx.elf");
    b.installArtifact(virt_rx);

    const virt_tx = sddf_dep.artifact("serial_virt_tx.elf");
    b.installArtifact(virt_tx);

    const serial_server = b.addExecutable(.{
        .name = "serial_server.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });

    serial_server.step.dependOn(meta_step);
    serial_server.addIncludePath(config_headers.items[0]);
    serial_server.addIncludePath(.{ .cwd_relative = b.getInstallPath(.prefix, "")});
    serial_server.addCSourceFile(.{ .file = b.path("serial_server.c") });
    serial_server.addIncludePath(sddf_dep.path("include"));
    serial_server.addIncludePath(b.path("include/serial_config"));
    serial_server.linkLibrary(sddf_dep.artifact("util"));
    serial_server.linkLibrary(sddf_dep.artifact("util_putchar_serial"));

    serial_server.addIncludePath(.{ .cwd_relative = libmicrokit_include });
    serial_server.addObjectFile(.{ .cwd_relative = libmicrokit });
    serial_server.setLinkerScript(.{ .cwd_relative = libmicrokit_linker_script });

    b.installArtifact(serial_server);

    const final_image_dest = b.getInstallPath(.bin, "./loader.img");
    const microkit_tool_cmd = b.addSystemCommand(&[_][]const u8{
        microkit_tool,
        b.getInstallPath(.prefix, "serial.system"),
        "--search-path", b.getInstallPath(.bin, ""),
        "--board", microkit_board,
        "--config", microkit_config,
        "-o", final_image_dest,
        "-r", b.getInstallPath(.prefix, "./report.txt")
    });
    microkit_tool_cmd.step.dependOn(b.getInstallStep());
    microkit_tool_cmd.step.dependOn(&driver_install.step);
    microkit_tool_cmd.setEnvironmentVariable("MICROKIT_SDK", microkit_sdk);
    microkit_tool_cmd.step.dependOn(&b.addInstallFileWithDir(sdf_file, .prefix, "serial.system").step);
    // Add the "microkit" step, and make it the default step when we execute `zig build`>
    const microkit_step = b.step("microkit", "Compile and build the final bootable image");
    microkit_step.dependOn(&microkit_tool_cmd.step);
    b.default_step = microkit_step;

    // This is setting up a `qemu` command for running the system using QEMU,
    // which we only want to do when we have a board that we can actually simulate.
    const loader_arg = b.fmt("loader,file={s},addr=0x70000000,cpu-num=0", .{final_image_dest});
    if (std.mem.eql(u8, microkit_board, "qemu_virt_aarch64")) {
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
