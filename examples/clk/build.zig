//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");

const MicrokitBoard = enum { odroidc4 };

const Target = struct {
    board: MicrokitBoard,
    zig_target: std.Target.Query,
};

const targets = [_]Target{
    .{
        .board = MicrokitBoard.odroidc4,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.arm.cpu.cortex_a55 },
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

    const dtb_arg = b.option([]const u8, "dtb", "Path to DTB file");
    if (dtb_arg == null) {
        std.log.err("Missing -Dsdk=/path/to/dtb argument being passed\n", .{});
        std.posix.exit(1);
    }
    const dtb_path = std.Build.LazyPath{ .cwd_relative = dtb_arg.? };
    const sddf_dep = b.dependency("sddf", .{
        .target = target,
        .optimize = optimize,
        .libmicrokit = @as([]const u8, libmicrokit),
        .libmicrokit_include = @as([]const u8, libmicrokit_include),
        .libmicrokit_linker_script = @as([]const u8, libmicrokit_linker_script),
        .i2c_client_include = @as([]const u8, ""),
        .clk_client_include = @as([]const u8, "include"),
        .dtb_path = @as([]const u8, dtb_path.getPath(b) ),
    });

    const timer_driver_class = switch (microkit_board_option.?) {
        .odroidc4 => "meson",
    };

    const clk_driver_class = switch (microkit_board_option.?) {
        .odroidc4 => "meson",
    };
    const clk_driver = sddf_dep.artifact(b.fmt("driver_clk_{s}.elf", .{clk_driver_class}));
    const clk_driver_install = b.addInstallArtifact(clk_driver, .{ .dest_sub_path = "clk_driver.elf" });

    const timer_driver = sddf_dep.artifact(b.fmt("driver_timer_{s}.elf", .{timer_driver_class}));
    // This is required because the SDF file is expecting a different name to the artifact we
    // are dealing with.
    const timer_driver_install = b.addInstallArtifact(timer_driver, .{ .dest_sub_path = "timer_driver.elf" });

    const client = b.addExecutable(.{
        .name = "client.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    client.addCSourceFile(.{ .file = b.path("client.c") });
    client.addIncludePath(sddf_dep.path("include"));
    client.linkLibrary(sddf_dep.artifact("util"));
    client.linkLibrary(sddf_dep.artifact("util_putchar_debug"));
    client.addIncludePath(.{ .cwd_relative = libmicrokit_include });
    client.addObjectFile(.{ .cwd_relative = libmicrokit });
    client.setLinkerScriptPath(.{ .cwd_relative = libmicrokit_linker_script });

    b.installArtifact(client);

    const system_description_path = b.fmt("board/{s}/clk.system", .{microkit_board});
    const final_image_dest = b.getInstallPath(.bin, "./loader.img");
    const microkit_tool_cmd = b.addSystemCommand(&[_][]const u8{
        microkit_tool,
        system_description_path,
        "--search-path", b.getInstallPath(.bin, ""),
        "--board", microkit_board,
        "--config", microkit_config,
        "-o", final_image_dest,
        "-r", b.getInstallPath(.prefix, "./report.txt") });
    microkit_tool_cmd.step.dependOn(b.getInstallStep());
    microkit_tool_cmd.step.dependOn(&timer_driver_install.step);
    microkit_tool_cmd.step.dependOn(&clk_driver_install.step);
    const microkit_step = b.step("microkit", "Compile and build the final bootable image");
    microkit_step.dependOn(&microkit_tool_cmd.step);
    b.default_step = microkit_step;
}
