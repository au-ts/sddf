//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");
const Step = std.Build.Step;
const LazyPath = std.Build.LazyPath;

const MicrokitBoard = enum {
    qemu_virt_aarch64,
    maaxboard,
    qemu_virt_riscv64,
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
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{ .strict_align }),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = .maaxboard,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{ .strict_align }),
            .os_tag = .freestanding,
            .abi = .none,
        },
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

fn updateSectionObjcopy(b: *std.Build, section: []const u8, data_output: std.Build.LazyPath, data: []const u8, elf: []const u8) *Step.Run {
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

    const partition = b.option(usize, "partition", "Block device partition for client to use") orelse null;

    // Getting the path to the Microkit SDK before doing anything else
    const microkit_sdk = b.option(LazyPath, "sdk", "Path to Microkit SDK") orelse {
        std.log.err("Missing -Dsdk=/path/to/sdk argument being passed\n", .{});
        std.posix.exit(1);
    };

    const microkit_config = b.option(ConfigOptions, "config", "Microkit config to build for") orelse ConfigOptions.debug;

    // Get the Microkit SDK board we want to target
    const microkit_board = b.option(MicrokitBoard, "board", "Microkit board to target") orelse {
        std.log.err("Missing -Dboard=<BOARD> argument being passed\n", .{});
        std.posix.exit(1);
    };
    const target = b.resolveTargetQuery(findTarget(microkit_board));

    const microkit_board_dir = microkit_sdk.path(b, b.fmt("board/{s}/{s}", .{ @tagName(microkit_board), @tagName(microkit_config) }));
    const microkit_tool = microkit_sdk.path(b, "bin/microkit");
    const libmicrokit = microkit_board_dir.path(b, "lib/libmicrokit.a");
    const libmicrokit_include = microkit_board_dir.path(b, "include");
    const libmicrokit_linker_script = microkit_board_dir.path(b, "lib/microkit.ld");

    const sddf_dep = b.dependency("sddf", .{
        .target = target,
        .optimize = optimize,
        .libmicrokit = libmicrokit,
        .libmicrokit_include = libmicrokit_include,
        .libmicrokit_linker_script = libmicrokit_linker_script,
    });

    const timer_driver_class = switch (microkit_board) {
        .maaxboard => "imx",
        else => null,
    };
    var timer_driver_install: ?*Step.InstallArtifact = null;
    if (timer_driver_class) |c| {
        const driver = sddf_dep.artifact(b.fmt("driver_timer_{s}.elf", .{ c }));
        // To match what our SDF expects
        timer_driver_install = b.addInstallArtifact(driver, .{ .dest_sub_path = "timer_driver.elf" });
    }

    const blk_driver_class = switch (microkit_board) {
        .qemu_virt_aarch64, .qemu_virt_riscv64 => "virtio",
        .maaxboard => "mmc_imx",
    };

    const client = b.addExecutable(.{
        .name = "client.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });

    client.addCSourceFiles(.{
        .files = &.{ "client.c" },
    });

    client.addIncludePath(sddf_dep.path("include"));
    client.addIncludePath(sddf_dep.path("include/microkit"));
    client.linkLibrary(sddf_dep.artifact("util"));
    client.linkLibrary(sddf_dep.artifact("util_putchar_debug"));

    client.addIncludePath(libmicrokit_include);
    client.addObjectFile(libmicrokit);
    client.setLinkerScript(libmicrokit_linker_script);

    const blk_driver = sddf_dep.artifact(b.fmt("driver_blk_{s}.elf", .{ blk_driver_class }));

    b.installArtifact(client);
    b.installArtifact(blk_driver);
    b.installArtifact(sddf_dep.artifact("blk_virt.elf"));

    // Because our SDF expects a different ELF name for the block driver, we have this extra step.
    const blk_driver_install = b.addInstallArtifact(blk_driver, .{ .dest_sub_path = "blk_driver.elf" });

    // For compiling the DTS into a DTB
    const dts = sddf_dep.path(b.fmt("dts/{s}.dts", .{@tagName(microkit_board)}));
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
    run_metaprogram.addArg(@tagName(microkit_board));
    run_metaprogram.addArg("--sdf");
    run_metaprogram.addArg("blk.system");
    if (partition) |p| {
        run_metaprogram.addArg("--partition");
        run_metaprogram.addArg(b.fmt("{}", .{ p }));
    }
    _ = try run_metaprogram.step.addDirectoryWatchInput(sddf_dep.path(""));

    const meta_output_install = b.addInstallDirectory(.{
        .source_dir = meta_output,
        .install_dir = .prefix,
        .install_subdir = "meta_output",
    });

    const client_objcopy = updateSectionObjcopy(b, ".blk_client_config", meta_output, "blk_client_client.data", "client.elf");
    const virt_objcopy = updateSectionObjcopy(b, ".blk_virt_config", meta_output, "blk_virt.data", "blk_virt.elf");
    const driver_resources_objcopy = updateSectionObjcopy(b, ".device_resources", meta_output, "blk_driver_device_resources.data", "blk_driver.elf");
    const driver_config_objcopy = updateSectionObjcopy(b, ".blk_driver_config", meta_output, "blk_driver.data", "blk_driver.elf");
    driver_resources_objcopy.step.dependOn(&blk_driver_install.step);
    driver_config_objcopy.step.dependOn(&blk_driver_install.step);
    const blk_objcopys = .{ client_objcopy, virt_objcopy, driver_resources_objcopy, driver_config_objcopy };
    const objcopys = blk: {
        if (timer_driver_install != null) {
            const blk_driver_timer_objcopy = updateSectionObjcopy(b, ".timer_client_config", meta_output, "timer_client_blk_driver.data", "blk_driver.elf");
            blk_driver_timer_objcopy.step.dependOn(&blk_driver_install.step);
            const timer_driver_objcopy = updateSectionObjcopy(b, ".device_resources", meta_output, "timer_driver_device_resources.data", "timer_driver.elf");
            timer_driver_objcopy.step.dependOn(&timer_driver_install.?.step);
            break :blk &(blk_objcopys ++ .{ blk_driver_timer_objcopy, timer_driver_objcopy });
        } else {
            break :blk &blk_objcopys;
        }
    };

    const final_image_dest = b.getInstallPath(.bin, "./loader.img");

    const microkit_tool_cmd = Step.Run.create(b, "run microkit tool");
    microkit_tool_cmd.addFileArg(microkit_tool);
    microkit_tool_cmd.addArgs(&[_][]const u8{
        b.getInstallPath(.{ .custom = "meta_output" }, "blk.system"),
        "--search-path", b.getInstallPath(.bin, ""),
        "--board", @tagName(microkit_board),
        "--config", @tagName(microkit_config),
        "-o", final_image_dest,
        "-r", b.getInstallPath(.prefix, "./report.txt"),
    });
    for (objcopys) |objcopy| {
        microkit_tool_cmd.step.dependOn(&objcopy.step);
    }
    microkit_tool_cmd.step.dependOn(&meta_output_install.step);
    microkit_tool_cmd.step.dependOn(b.getInstallStep());
    microkit_tool_cmd.setEnvironmentVariable("MICROKIT_SDK", microkit_sdk.getPath3(b, null).toString(b.allocator) catch @panic("OOM"));

    const microkit_step = b.step("microkit", "Compile and build the final bootable image");
    microkit_step.dependOn(&microkit_tool_cmd.step);
    b.default_step = microkit_step;

    // This is setting up a `qemu` command for running the system using QEMU,
    // which we only want to do when we have a board that we can actually simulate.
    if (microkit_board == .qemu_virt_aarch64 or microkit_board == .qemu_virt_riscv64) {
        const create_disk_cmd = b.addSystemCommand(&[_][]const u8{
            "bash",
        });
        const mkvirtdisk = sddf_dep.path("tools/mkvirtdisk");
        create_disk_cmd.addFileArg(mkvirtdisk);
        create_disk_cmd.addFileInput(mkvirtdisk);
        const disk = create_disk_cmd.addOutputFileArg("disk");
        create_disk_cmd.addArgs(&[_][]const u8{
            "1", "512", b.fmt("{}", .{ 1024 * 1024 * 16 }), "GPT",
        });
        const disk_install = b.addInstallFile(disk, "disk");
        disk_install.step.dependOn(&create_disk_cmd.step);

        var qemu_cmd: *Step.Run = undefined;
        if (microkit_board == .qemu_virt_aarch64) {
            const loader_arg = b.fmt("loader,file={s},addr=0x70000000,cpu-num=0", .{ final_image_dest });
            qemu_cmd = b.addSystemCommand(&[_][]const u8{
                "qemu-system-aarch64",
                "-machine", "virt,virtualization=on",
                "-cpu", "cortex-a53",
                "-serial", "mon:stdio",
                "-device", loader_arg,
                "-m", "2G",
                "-nographic",
            });
        } else if (microkit_board == .qemu_virt_riscv64) {
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
                "-nographic",
            });
        }

        const blk_device_args = &.{
            "-global", "virtio-mmio.force-legacy=false",
            "-drive", b.fmt("file={s},if=none,format=raw,id=hd", .{ b.getInstallPath(.prefix, "disk") }),
            "-device", "virtio-blk-device,drive=hd",
        };
        qemu_cmd.addArgs(blk_device_args);

        qemu_cmd.step.dependOn(b.default_step);
        qemu_cmd.step.dependOn(&disk_install.step);

        const simulate_step = b.step("qemu", "Simulate the image using QEMU");
        simulate_step.dependOn(&qemu_cmd.step);
    }
}
