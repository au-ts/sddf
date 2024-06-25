const std = @import("std");
const LazyPath = std.Build.LazyPath;

const DriverClass = struct {
    const Uart = enum {
        arm,
        meson,
        imx,
    };

    const Timer = enum {
        arm,
        meson,
        imx,
    };

    const I2c = enum {
        meson,
    };
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
    "util/assert.c",
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
    class: DriverClass.Uart,
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

fn addTimerDriver(
    b: *std.Build,
    util: *std.Build.Step.Compile,
    class: DriverClass.Timer,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
) *std.Build.Step.Compile {
    const driver = addPd(b, .{
        .name = b.fmt("driver_timer_{s}.elf", .{ @tagName(class) }),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/clock/{s}/timer.c", .{ @tagName(class) });
    driver.addCSourceFile(.{
        .file = b.path(source),
        .flags = &.{ "-fno-sanitize=undefined" }
    });
    driver.addIncludePath(b.path("include"));
    driver.linkLibrary(util);

    return driver;
}

fn addI2cDriver(
    b: *std.Build,
    util: *std.Build.Step.Compile,
    class: DriverClass.I2c,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
) *std.Build.Step.Compile {
    const driver = addPd(b, .{
        .name = b.fmt("driver_i2c_{s}.elf", .{ @tagName(class) }),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/i2c/{s}/i2c.c", .{ @tagName(class) });
    driver.addCSourceFile(.{
        .file = b.path(source),
        // Note: the I2C_BUS_NUM flag is temporary
        .flags = &.{ "-fno-sanitize=undefined", "-DI2C_BUS_NUM=2" }
    });
    driver.addIncludePath(b.path(b.fmt("drivers/i2c/{s}/", .{ @tagName(class) })));
    driver.addIncludePath(b.path("include"));
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

    const libmicrokit_opt = b.option([]const u8, "libmicrokit", "Path to libmicrokit.a") orelse null;
    const libmicrokit_include_opt = b.option([]const u8, "libmicrokit_include", "Path to the libmicrokit include directory") orelse null;
    const libmicrokit_linker_script_opt = b.option([]const u8, "libmicrokit_linker_script", "Path to the libmicrokit linker script") orelse null;
    const blk_num_clients_opt = b.option(u32, "blk_num_clients", "Number of block clients") orelse 2;
    const serial_config_include_option = b.option([]const u8, "serial_config_include", "Include path to serial config header") orelse "";

    // TODO: sort out
    const serial_config_include = LazyPath{ .cwd_relative = serial_config_include_option };
    // libmicrokit
    // We're declaring explicitly here instead of with anonymous structs due to a bug. See https://github.com/ziglang/zig/issues/19832
    libmicrokit = LazyPath{ .cwd_relative = libmicrokit_opt.? };
    libmicrokit_include = LazyPath{ .cwd_relative = libmicrokit_include_opt.? };
    libmicrokit_linker_script = LazyPath{ .cwd_relative = libmicrokit_linker_script_opt.? };


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
    blk_virt.addCSourceFile(.{ .file = b.path("blk/components/virt.c"), .flags = &.{b.fmt("-DBLK_NUM_CLIENTS={any}", .{blk_num_clients_opt})} });
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
    serial_virt_rx.addCSourceFile(.{
        .file = b.path("serial/components/virt_rx.c"),
        .flags = &.{"-fno-sanitize=undefined"}
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
    serial_virt_tx.addCSourceFile(.{
        .file = b.path("serial/components/virt_tx.c"),
        .flags = &.{"-fno-sanitize=undefined"}
    });
    serial_virt_tx.addIncludePath(serial_config_include);
    serial_virt_tx.addIncludePath(b.path("include"));
    serial_virt_tx.linkLibrary(util);
    serial_virt_tx.linkLibrary(util_putchar_debug);
    b.installArtifact(serial_virt_tx);

    // UART drivers
    inline for (std.meta.fields(DriverClass.Uart)) |class| {
        const driver = addUartDriver(b, serial_config_include, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    // Timer drivers
    inline for (std.meta.fields(DriverClass.Timer)) |class| {
        const driver = addTimerDriver(b, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    // I2C components
    const i2c_virt = addPd(b, .{
        .name = "i2c_virt.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    i2c_virt.addCSourceFile(.{
        .file = b.path("i2c/components/virt.c"),
        .flags = &.{"-fno-sanitize=undefined"}
    });
    i2c_virt.addIncludePath(b.path("include"));
    i2c_virt.linkLibrary(util);
    i2c_virt.linkLibrary(util_putchar_debug);
    b.installArtifact(i2c_virt);

    // I2C drivers
    inline for (std.meta.fields(DriverClass.I2c)) |class| {
        const driver = addI2cDriver(b, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    // sDDF headers
    // TODO: Investigate how to get this step to run when it is not an artifact/module/file
    // Not sure how to when this is exposed as a dependency to another build file
    // const sddf_headers = b.addInstallHeaderFile(b.path("include"), "sddf");
    // b.getInstallStep().dependOn(&sddf_headers.step);
}
