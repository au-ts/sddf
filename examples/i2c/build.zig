//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");
const LazyPath = std.Build.LazyPath;
const Step = std.Build.Step;

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
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a55 },
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

fn updateSectionObjcopy(b: *std.Build, section: []const u8, data_output: std.Build.LazyPath, data: []const u8, elf: []const u8) *Step.Run {
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
    });

    const i2c_driver_class = switch (microkit_board_option) {
        .odroidc4 => "meson",
    };

    const serial_driver_class = switch (microkit_board_option) {
        .odroidc4 => "meson",
    };

    const timer_driver_class = switch (microkit_board_option) {
        .odroidc4 => "meson",
    };

    const timer_driver = sddf_dep.artifact(b.fmt("driver_timer_{s}.elf", .{timer_driver_class}));
    // This is required because the SDF file is expecting a different name to the artifact we
    // are dealing with.
    const timer_driver_install = b.addInstallArtifact(timer_driver, .{ .dest_sub_path = "timer_driver.elf" });

    const serial_driver = sddf_dep.artifact(b.fmt("driver_serial_{s}.elf", .{serial_driver_class}));
    // This is required because the SDF file is expecting a different name to the artifact we
    // are dealing with.
    const serial_driver_install = b.addInstallArtifact(serial_driver, .{ .dest_sub_path = "serial_driver.elf" });

    const pn532_driver = sddf_dep.artifact("driver_i2c_device_pn532");
    const ds3231_driver = sddf_dep.artifact("driver_i2c_device_ds3231");

    const i2c_driver = sddf_dep.artifact(b.fmt("driver_i2c_{s}.elf", .{i2c_driver_class}));
    // This is required because the SDF file is expecting a different name to the artifact we
    // are dealing with.
    const i2c_driver_install = b.addInstallArtifact(i2c_driver, .{ .dest_sub_path = "i2c_driver.elf" });

    const client_pn532 = b.addExecutable(.{
        .name = "client_pn532.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });

    client_pn532.addCSourceFiles(.{
        .files = &.{"client_pn532.c"},
    });
    client_pn532.addIncludePath(sddf_dep.path("include"));
    client_pn532.addIncludePath(sddf_dep.path("include/microkit"));
    client_pn532.linkLibrary(sddf_dep.artifact("util"));
    client_pn532.linkLibrary(sddf_dep.artifact("util_putchar_serial"));
    client_pn532.linkLibrary(pn532_driver);

    const client_ds3231 = b.addExecutable(.{
        .name = "client_ds3231.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });

    client_ds3231.addCSourceFiles(.{
        .files = &.{"client_ds3231.c"},
    });
    client_ds3231.addIncludePath(sddf_dep.path("include"));
    client_ds3231.addIncludePath(sddf_dep.path("include/microkit"));
    client_ds3231.linkLibrary(sddf_dep.artifact("util"));
    client_ds3231.linkLibrary(sddf_dep.artifact("util_putchar_serial"));
    client_ds3231.linkLibrary(ds3231_driver);

    // Here we compile libco. Right now this is the only example that uses libco and so
    // we just compile it here instead of in a separate build.zig
    client_pn532.addIncludePath(sddf_dep.path("libco"));
    client_pn532.addCSourceFile(.{ .file = sddf_dep.path("libco/libco.c") });

    client_pn532.addIncludePath(libmicrokit_include);
    client_pn532.addObjectFile(libmicrokit);
    client_pn532.setLinkerScript(libmicrokit_linker_script);

    client_ds3231.addIncludePath(sddf_dep.path("libco"));
    client_ds3231.addCSourceFile(.{ .file = sddf_dep.path("libco/libco.c") });

    client_ds3231.addIncludePath(libmicrokit_include);
    client_ds3231.addObjectFile(libmicrokit);
    client_ds3231.setLinkerScript(libmicrokit_linker_script);

    b.installArtifact(client_pn532);
    b.installArtifact(client_ds3231);
    b.installArtifact(sddf_dep.artifact("i2c_virt.elf"));
    b.installArtifact(sddf_dep.artifact("serial_virt_tx.elf"));

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
    run_metaprogram.addArg("i2c.system");

    const meta_output_install = b.addInstallDirectory(.{
        .source_dir = meta_output,
        .install_dir = .prefix,
        .install_subdir = "meta_output",
    });

    const serial_driver_resources_objcopy = updateSectionObjcopy(b, ".device_resources", meta_output, "serial_driver_device_resources.data", "serial_driver.elf");
    const serial_driver_config_objcopy = updateSectionObjcopy(b, ".serial_driver_config", meta_output, "serial_driver_config.data", "serial_driver.elf");
    const serial_virt_objcopy = updateSectionObjcopy(b, ".serial_virt_tx_config", meta_output, "serial_virt_tx.data", "serial_virt_tx.elf");
    serial_driver_resources_objcopy.step.dependOn(&serial_driver_install.step);
    serial_driver_config_objcopy.step.dependOn(&serial_driver_install.step);
    const client_ds3231_serial_objcopy = updateSectionObjcopy(b, ".serial_client_config", meta_output, "serial_client_client_ds3231.data", "client_ds3231.elf");
    const client_pn532_serial_objcopy = updateSectionObjcopy(b, ".serial_client_config", meta_output, "serial_client_client_pn532.data", "client_pn532.elf");

    const timer_driver_objcopy = updateSectionObjcopy(b, ".device_resources", meta_output, "timer_driver_device_resources.data", "timer_driver.elf");
    timer_driver_objcopy.step.dependOn(&timer_driver_install.step);
    const client_ds3231_timer_objcopy = updateSectionObjcopy(b, ".timer_client_config", meta_output, "timer_client_client_ds3231.data", "client_ds3231.elf");
    const client_pn532_timer_objcopy = updateSectionObjcopy(b, ".timer_client_config", meta_output, "timer_client_client_pn532.data", "client_pn532.elf");

    const i2c_driver_device_objcopy = updateSectionObjcopy(b, ".device_resources", meta_output, "i2c_driver_device_resources.data", "i2c_driver.elf");
    i2c_driver_device_objcopy.step.dependOn(&i2c_driver_install.step);
    const i2c_driver_config_objcopy = updateSectionObjcopy(b, ".i2c_driver_config", meta_output, "i2c_driver.data", "i2c_driver.elf");
    i2c_driver_config_objcopy.step.dependOn(&i2c_driver_install.step);
    const i2c_virt_objcopy = updateSectionObjcopy(b, ".i2c_virt_config", meta_output, "i2c_virt.data", "i2c_virt.elf");
    const client_ds3231_i2c_objcopy = updateSectionObjcopy(b, ".i2c_client_config", meta_output, "i2c_client_client_ds3231.data", "client_ds3231.elf");
    const client_pn532_i2c_objcopy = updateSectionObjcopy(b, ".i2c_client_config", meta_output, "i2c_client_client_pn532.data", "client_pn532.elf");

    const objcopys = &.{
        serial_driver_resources_objcopy,
        serial_driver_config_objcopy,
        serial_virt_objcopy,
        client_ds3231_serial_objcopy,
        client_pn532_serial_objcopy,
        client_ds3231_i2c_objcopy,
        client_ds3231_timer_objcopy,
        client_pn532_i2c_objcopy,
        client_pn532_timer_objcopy,
        i2c_virt_objcopy,
        i2c_driver_device_objcopy,
        i2c_driver_config_objcopy,
        timer_driver_objcopy,
    };

    const final_image_dest = b.getInstallPath(.bin, "./loader.img");
    const microkit_tool_cmd = Step.Run.create(b, "run microkit tool");
    microkit_tool_cmd.addFileArg(microkit_tool);
    microkit_tool_cmd.addArgs(&[_][]const u8{
        b.getInstallPath(.{ .custom = "meta_output" }, "i2c.system"),
        // zig fmt: off
        "--search-path", b.getInstallPath(.bin, ""),
        "--board", microkit_board,
        "--config", microkit_config,
        "-o", final_image_dest,
        "-r", b.getInstallPath(.prefix, "./report.txt"),
        // zig fmt: on
    });
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
