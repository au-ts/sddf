//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");
const LazyPath = std.Build.LazyPath;
const Step = std.Build.Step;

const MicrokitBoard = enum {
    maaxboard,
};

const Target = struct {
    board: MicrokitBoard,
    zig_target: std.Target.Query,
};

const targets = [_]Target{
    .{
        .board = MicrokitBoard.maaxboard,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{.strict_align}),
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

fn updateSectionObjcopy(b: *std.Build, section: []const u8, data_output: std.Build.LazyPath, data: []const u8, elf: []const u8) *std.Build.Step.Run {
    const run_objcopy = b.addSystemCommand(&[_][]const u8{
        "llvm-objcopy",
    });
    run_objcopy.addArg("--update-section");
    const data_full_path = data_output.join(b.allocator, data) catch @panic("OOM");
    run_objcopy.addPrefixedFileArg(b.fmt("{s}=", .{section}), data_full_path);
    run_objcopy.addFileArg(.{ .cwd_relative = b.getInstallPath(.bin, elf) });

    // We need the ELFs we talk about to be in the install directory first.
    run_objcopy.step.dependOn(b.getInstallStep());

    return run_objcopy;
}

pub fn build(b: *std.Build) !void {
    const optimize = b.standardOptimizeOption(.{});

    const default_python = if (std.posix.getenv("PYTHON")) |p| p else "python3";
    const python = b.option([]const u8, "python", "Path to Python to use") orelse default_python;

    const microkit_sdk = b.option(LazyPath, "sdk", "Path to Microkit SDK") orelse {
        std.log.err("Missing -Dsdk=<sdk> argument", .{});
        return error.MissingSdkPath;
    };

    const microkit_config_option = b.option(ConfigOptions, "config", "Microkit config to build for") orelse .debug;
    const microkit_config = @tagName(microkit_config_option);

    const microkit_board_option = b.option(MicrokitBoard, "board", "Microkit board to target") orelse {
        std.log.err("Missing -Dboard=<board> argument", .{});
        return error.MissingBoard;
    };

    const target = b.resolveTargetQuery(findTarget(microkit_board_option));
    const microkit_board = @tagName(microkit_board_option);

    const microkit_board_dir = microkit_sdk.path(b, "board").path(b, microkit_board).path(b, microkit_config);
    const microkit_tool = microkit_sdk.path(b, "bin/microkit");
    const libmicrokit = microkit_board_dir.path(b, "lib/libmicrokit.a");
    const libmicrokit_include = microkit_board_dir.path(b, "include");
    const libmicrokit_linker_script = microkit_board_dir.path(b, "lib/microkit.ld");

    const sddf_dep = b.dependency("sddf", .{
        .target = target,
        .optimize = optimize,
        .microkit_board_dir = microkit_board_dir,
        .gpio_config_include = @as([]const u8, "include"),
    });

    const driver_class = switch (microkit_board_option) {
        .maaxboard => "imx",
    };

    const driver = sddf_dep.artifact(b.fmt("driver_gpio_{s}.elf", .{driver_class}));
    // This is required because the SDF file is expecting a different name to the artifact we
    // are dealing with.
    const driver_install = b.addInstallArtifact(driver, .{ .dest_sub_path = "gpio_driver.elf" });

    const client = b.addExecutable(.{
        .name = "client.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });

    client.addCSourceFile(.{ .file = b.path("client.c") });

    // For gpio_config.h
    client.addIncludePath(b.path("include"));

    client.addIncludePath(sddf_dep.path("include"));
    client.addIncludePath(sddf_dep.path("include/microkit"));
    client.addIncludePath(sddf_dep.path("examples/gpio"));
    client.linkLibrary(sddf_dep.artifact("util"));
    client.linkLibrary(sddf_dep.artifact("util_putchar_debug"));

    // for coroutines in client
    client.addIncludePath(sddf_dep.path("libco"));
    client.addCSourceFile(.{ .file = sddf_dep.path("libco/libco.c") });

    client.addIncludePath(libmicrokit_include);
    client.addObjectFile(libmicrokit);
    client.setLinkerScript(libmicrokit_linker_script);

    b.installArtifact(client);

    // For compiling the DTS into a DTB
    const dts = sddf_dep.path(b.fmt("dts/{s}.dts", .{microkit_board}));
    const dtc_cmd = b.addSystemCommand(&[_][]const u8{ "dtc", "-q", "-I", "dts", "-O", "dtb" });
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
    run_metaprogram.addArg("gpio.system");

    const meta_output_install = b.addInstallDirectory(.{
        .source_dir = meta_output,
        .install_dir = .prefix,
        .install_subdir = "meta_output",
    });

    const client_objcopy = updateSectionObjcopy(b, ".gpio_client_config", meta_output, "gpio_client_client.data", "client.elf");
    const driver_objcopy = updateSectionObjcopy(b, ".device_resources", meta_output, "gpio_driver_device_resources.data", "gpio_driver.elf");
    driver_objcopy.step.dependOn(&driver_install.step);
    const objcopys = &.{ client_objcopy, driver_objcopy };

    const final_image_dest = b.getInstallPath(.bin, "./loader.img");
    const microkit_tool_cmd = Step.Run.create(b, "run microkit tool");
    microkit_tool_cmd.addFileArg(microkit_tool);
    microkit_tool_cmd.addArgs(&[_][]const u8{ b.getInstallPath(.{ .custom = "meta_output" }, "gpio.system"), "--search-path", b.getInstallPath(.bin, ""), "--board", microkit_board, "--config", microkit_config, "-o", final_image_dest, "-r", b.getInstallPath(.prefix, "./report.txt") });
    inline for (objcopys) |objcopy| {
        microkit_tool_cmd.step.dependOn(&objcopy.step);
    }
    microkit_tool_cmd.step.dependOn(&meta_output_install.step);
    microkit_tool_cmd.step.dependOn(b.getInstallStep());
    microkit_tool_cmd.setEnvironmentVariable("MICROKIT_SDK", microkit_sdk.getPath3(b, null).toString(b.allocator) catch @panic("OOM"));

    const microkit_step = b.step("microkit", "Compile and build the final bootable image");
    microkit_step.dependOn(&microkit_tool_cmd.step);
    b.default_step = microkit_step;
}
