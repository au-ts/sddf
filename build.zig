const std = @import("std");
const LazyPath = std.Build.LazyPath;

const MicrokitBoard = enum {
    qemu_arm_virt,
    odroidc4,
    maaxboard
};

const ConfigOptions = enum {
    debug,
    release,
    benchmark
};

const DriverUart = enum {
    arm,
    meson,
    imx,
};

const util_src = [_][]const u8{
    "util/newlibc.c",
    "util/cache.c",
    // TODO:
    // should these device specific utils be here?
    // or maybe move these into the outer util directory
    "blk/util/fsmalloc.c",
    "blk/util/bitarray.c",
    // "blk/util/util.c",
};

const util_putchar_debug_src = [_][]const u8{
    "util/assert.c",
    "util/printf.c",
    "util/putchar_debug.c",
};

const util_putchar_serial_src = [_][]const u8{
    "util/assert.c",
    "util/printf.c",
    "util/putchar_serial.c",
};

var libmicrokit: std.Build.LazyPath = undefined;
var libmicrokit_linker_script: std.Build.LazyPath = undefined;
var libmicrokit_include: std.Build.LazyPath = undefined;

fn addUartDriver(
    b: *std.Build,
    serial_config_include: LazyPath,
    util: *std.Build.Step.Compile,
    class: DriverUart,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
) *std.Build.Step.Compile {
    const driver = addPd(b, .{
        .name = b.fmt("driver_uart_{s}.elf", .{ @tagName(class) }),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/serial/{s}/uart.c", .{ @tagName(class) });
    const driver_include = b.fmt("drivers/serial/{s}/include", .{ @tagName(class) });
    driver.addCSourceFile(.{
        .file = b.path(source),
        .flags = &.{ "-fno-sanitize=undefined" }
    });
    driver.addIncludePath(b.path("include"));
    driver.addIncludePath(b.path(driver_include));
    driver.addIncludePath(serial_config_include);
    driver.linkLibrary(util);

    return driver;
}

fn addPd(b: *std.Build, options: std.Build.ExecutableOptions) *std.Build.Step.Compile {
    const pd = b.addExecutable(options);
    pd.addObjectFile(libmicrokit);
    pd.setLinkerScriptPath(libmicrokit_linker_script);
    pd.addIncludePath(libmicrokit_include);

    return pd;
}

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    // Microkit SDK option
    const microkit_sdk_option_tmp = b.option([]const u8, "sdk", "Path to Microkit SDK");
    if (microkit_sdk_option_tmp == null) {
        std.log.err("Missing -Dsdk=/path/to/sdk argument being passed\n", .{});
        std.posix.exit(1);
    }
    const microkit_sdk_option = microkit_sdk_option_tmp.?;
    std.fs.cwd().access(microkit_sdk_option, .{}) catch |err| {
        switch (err) {
            error.FileNotFound => std.log.err("Path to SDK '{s}' does not exist\n", .{ microkit_sdk_option }),
            else => std.log.err("Could not acccess SDK path '{s}', error is {any}\n", .{ microkit_sdk_option, err })
        }
        std.posix.exit(1);
    };

    // Microkit config option
    const microkit_config_option = b.option(ConfigOptions, "config", "Microkit config to build for") orelse ConfigOptions.debug;

    // Microkit board option
    const microkit_board_option_tmp = b.option(MicrokitBoard, "board", "Microkit board to target");
    if (microkit_board_option_tmp == null) {
        std.log.err("Missing -Dboard=<BOARD> argument being passed\n", .{});
        std.posix.exit(1);
    }
    const microkit_board_option = microkit_board_option_tmp.?;
    const microkit_board_dir = b.fmt("{s}/board/{s}/{s}", .{ microkit_sdk_option, @tagName(microkit_board_option), @tagName(microkit_config_option) });
    std.fs.cwd().access(microkit_board_dir, .{}) catch |err| {
        switch (err) {
            error.FileNotFound => std.log.err("Path to '{s}' does not exist\n", .{ microkit_board_dir }),
            else => std.log.err("Could not acccess path '{s}', error is {any}\n", .{ microkit_board_dir, err })
        }
        std.posix.exit(1);
    };

    const serial_config_include_option = b.option([]const u8, "serial_config_include", "Include path to serial config header") orelse null;
    // TODO: sort out
    const serial_config_include = LazyPath{ .cwd_relative = serial_config_include_option.? };

    // libmicrokit
    // We're declaring explicitly here instead of with anonymous structs due to a bug. See https://github.com/ziglang/zig/issues/19832
    libmicrokit = LazyPath{ .cwd_relative = b.fmt("{s}/lib/libmicrokit.a", .{ microkit_board_dir }) };
    libmicrokit_linker_script = LazyPath{ .cwd_relative = b.fmt("{s}/lib/microkit.ld", .{ microkit_board_dir }) };
    libmicrokit_include = LazyPath{ .cwd_relative = b.fmt("{s}/include", .{ microkit_board_dir }) };

    // util libraries
    const util = b.addStaticLibrary(.{
        .name = "util",
        .target = target,
        .optimize = optimize,
    });
    util.addCSourceFiles(.{
        .files = &util_src,
        .flags = &.{"-fno-sanitize=undefined"},
    });
    util.addIncludePath(b.path("include"));
    util.addIncludePath(libmicrokit_include);
    util.installHeadersDirectory(b.path("include"), "", .{});
    b.installArtifact(util);

    const util_putchar_serial = b.addStaticLibrary(.{
        .name = "util_putchar_serial",
        .target = target,
        .optimize = optimize,
    });
    util_putchar_serial.addCSourceFiles(.{
        .files = &util_putchar_serial_src,
        .flags = &.{"-fno-sanitize=undefined"},
    });
    util_putchar_serial.addIncludePath(b.path("include"));
    util_putchar_serial.addIncludePath(libmicrokit_include);
    util_putchar_serial.installHeadersDirectory(b.path("include"), "", .{});
    b.installArtifact(util_putchar_serial);

    const util_putchar_debug = b.addStaticLibrary(.{
        .name = "util_putchar_debug",
        .target = target,
        .optimize = optimize,
    });
    util_putchar_debug.addCSourceFiles(.{
        .files = &util_putchar_debug_src,
        .flags = &.{"-fno-sanitize=undefined"},
    });
    util_putchar_debug.addIncludePath(b.path("include"));
    util_putchar_debug.addIncludePath(libmicrokit_include);
    util_putchar_debug.installHeadersDirectory(b.path("include"), "", .{});
    b.installArtifact(util_putchar_debug);

    // Block components
    const blk_virt = addPd(b, .{
        .name = "blk_virt.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    // TODO: This flag -DBLK_NUM_CLIENTS needs to be configurable by the user of this dependency
    blk_virt.addCSourceFile(.{ .file = b.path("blk/components/virt.c"), .flags = &.{"-DBLK_NUM_CLIENTS=2"} });
    blk_virt.addCSourceFiles(.{ .files = &.{ "blk/util/bitarray.c", "blk/util/fsmalloc.c", "blk/util/util.c", "util/cache.c" } });
    blk_virt.addIncludePath(b.path("include"));
    blk_virt.linkLibrary(util_putchar_debug);
    b.installArtifact(blk_virt);

    // Serial components
    const serial_virt_rx = addPd(b, .{
        .name = "serial_virt_rx.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    // TODO: This flag -DSERIAL_NUM_CLIENTS=3 needs to be configurable by the user of this dependency
    serial_virt_rx.addCSourceFile(.{
        .file = b.path("serial/components/virt_rx.c"),
        .flags = &.{"-DSERIAL_NUM_CLIENTS=3", "-fno-sanitize=undefined"}
    });
    serial_virt_rx.addIncludePath(serial_config_include);
    serial_virt_rx.addIncludePath(b.path("include"));
    serial_virt_rx.linkLibrary(util);
    serial_virt_rx.linkLibrary(util_putchar_debug);
    b.installArtifact(serial_virt_rx);

    const serial_virt_tx = addPd(b, .{
        .name = "serial_virt_tx.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    // TODO: This flag -DSERIAL_NUM_CLIENTS=3 -DSERIAL_TRANSFER_WITH_COLOUR needs to be configurable by the user of this dependency
    serial_virt_tx.addCSourceFile(.{
        .file = b.path("serial/components/virt_tx.c"),
        .flags = &.{"-DSERIAL_NUM_CLIENTS=3", "-DSERIAL_TRANSFER_WITH_COLOUR", "-fno-sanitize=undefined"}
    });
    serial_virt_tx.addIncludePath(serial_config_include);
    serial_virt_tx.addIncludePath(b.path("include"));
    serial_virt_tx.linkLibrary(util);
    serial_virt_tx.linkLibrary(util_putchar_debug);
    b.installArtifact(serial_virt_tx);

    // UART drivers
    inline for (std.meta.fields(DriverUart)) |class| {
        const driver = addUartDriver(b, serial_config_include, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    // sDDF headers
    // TODO: Investigate how to get this step to run when it is not an artifact/module/file
    // Not sure how to when this is exposed as a dependency to another build file
    // const sddf_headers = b.addInstallHeaderFile(b.path("include"), "sddf");
    // b.getInstallStep().dependOn(&sddf_headers.step);
}
