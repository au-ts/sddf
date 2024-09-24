//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");
const LazyPath = std.Build.LazyPath;

const DriverClass = struct {
    const Uart = enum {
        arm,
        meson,
        imx,
        snps,
    };

    const Timer = enum {
        arm,
        meson,
        imx,
        jh7110,
    };

    const Network = enum {
        imx,
        meson,
        virtio
    };

    const I2cHost = enum {
        meson,
    };

    const Block = enum {
        virtio,
    };

    const Mmc = enum {
        imx,
    };

    const I2cDevice = enum {
        ds3231,
        pn532,
    };
};

const util_src = [_][]const u8{
    "util/newlibc.c",
    "util/cache.c",
    "util/fsmalloc.c",
    "util/bitarray.c",
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
        .name = b.fmt("driver_uart_{s}.elf", .{@tagName(class)}),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/serial/{s}/uart.c", .{@tagName(class)});
    const driver_include = b.fmt("drivers/serial/{s}/include", .{@tagName(class)});
    driver.addCSourceFile(.{
        .file = b.path(source),
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
        .name = b.fmt("driver_timer_{s}.elf", .{@tagName(class)}),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/timer/{s}/timer.c", .{ @tagName(class) });
    driver.addCSourceFile(.{
        .file = b.path(source),
    });
    driver.addIncludePath(b.path("include"));
    driver.linkLibrary(util);

    return driver;
}

fn addI2cDriverDevice(
    b: *std.Build,
    util: *std.Build.Step.Compile,
    device: DriverClass.I2cDevice,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    i2c_client_include: LazyPath,
) *std.Build.Step.Compile {
    const driver = b.addStaticLibrary(.{
        .name = b.fmt("driver_i2c_device_{s}", .{@tagName(device)}),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    driver.addIncludePath(libmicrokit_include);
    const source = b.fmt("i2c/devices/{s}/{s}.c", .{ @tagName(device), @tagName(device) });
    driver.addCSourceFile(.{
        .file = b.path(source),
    });
    driver.addIncludePath(b.path(b.fmt("i2c/devices/{s}/", .{@tagName(device)})));
    driver.addIncludePath(b.path("include"));
    driver.linkLibrary(util);
    driver.addIncludePath(b.path("libco"));
    driver.addIncludePath(i2c_client_include);

    return driver;
}

fn addI2cDriverHost(
    b: *std.Build,
    util: *std.Build.Step.Compile,
    class: DriverClass.I2cHost,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
) *std.Build.Step.Compile {
    const driver = addPd(b, .{
        .name = b.fmt("driver_i2c_{s}.elf", .{@tagName(class)}),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/i2c/{s}/i2c.c", .{@tagName(class)});
    driver.addCSourceFile(.{
        .file = b.path(source),
        // Note: the I2C_BUS_NUM flag is temporary
        .flags = &.{"-DI2C_BUS_NUM=2"},
    });
    driver.addIncludePath(b.path(b.fmt("drivers/i2c/{s}/", .{@tagName(class)})));
    driver.addIncludePath(b.path("include"));
    driver.linkLibrary(util);

    return driver;
}

fn addBlockDriver(
    b: *std.Build,
    blk_config_include: LazyPath,
    util: *std.Build.Step.Compile,
    class: DriverClass.Block,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
) *std.Build.Step.Compile {
    const driver = addPd(b, .{
        .name = b.fmt("driver_blk_{s}.elf", .{ @tagName(class) }),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/blk/{s}/block.c", .{ @tagName(class) });
    driver.addCSourceFile(.{
        .file = b.path(source),
    });
    driver.addIncludePath(blk_config_include);
    driver.addIncludePath(b.path(b.fmt("drivers/blk/{s}/", .{ @tagName(class) })));
    driver.addIncludePath(b.path("include"));
    driver.linkLibrary(util);

    return driver;
}

fn addMmcDriver(
    b: *std.Build,
    blk_config_include: LazyPath,
    util: *std.Build.Step.Compile,
    class: DriverClass.Mmc,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
) *std.Build.Step.Compile {
    const driver = addPd(b, .{
        .name = b.fmt("driver_blk_mmc_{s}.elf", .{ @tagName(class) }),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/blk/mmc/{s}/usdhc.c", .{ @tagName(class) });
    driver.addCSourceFile(.{
        .file = b.path(source),
    });
    driver.addIncludePath(blk_config_include);
    driver.addIncludePath(b.path(b.fmt("drivers/blk/mmc/{s}/", .{ @tagName(class) })));
    driver.addIncludePath(b.path("include"));
    driver.linkLibrary(util);

    return driver;
}

fn addNetworkDriver(
    b: *std.Build,
    net_config_include: LazyPath,
    util: *std.Build.Step.Compile,
    class: DriverClass.Network,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
) *std.Build.Step.Compile {
    const driver = addPd(b, .{
        .name = b.fmt("driver_net_{s}.elf", .{ @tagName(class) }),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/network/{s}/ethernet.c", .{ @tagName(class) });
    driver.addCSourceFile(.{
        .file = b.path(source),
    });
    driver.addIncludePath(net_config_include);
    driver.addIncludePath(b.path(b.fmt("drivers/network/{s}/", .{ @tagName(class) })));
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
    const blk_config_include_opt = b.option([]const u8, "blk_config_include", "Include path to block config header") orelse "";
    const serial_config_include_option = b.option([]const u8, "serial_config_include", "Include path to serial config header") orelse "";
    const net_config_include_option = b.option([]const u8, "net_config_include", "Include path to network config header") orelse "";
    const i2c_client_include_option = b.option([]const u8, "i2c_client_include", "Include path to client config header") orelse "";

    // TODO: Right now this is not super ideal. What's happening is that we do not
    // always need a serial config include, but we must always specify it
    // as a build option. What we do instead is just make the include path an
    // empty string if it has not been provided, which could be an annoying to
    // debug error if you do need a serial config but forgot to pass one in.
    const serial_config_include = LazyPath{ .cwd_relative = serial_config_include_option };
    const blk_config_include = LazyPath{ .cwd_relative = blk_config_include_opt };
    const net_config_include = LazyPath{ .cwd_relative = net_config_include_option };
    const i2c_client_include = LazyPath{ .cwd_relative = i2c_client_include_option };
    // libmicrokit
    // We're declaring explicitly here instead of with anonymous structs due to a bug. See https://github.com/ziglang/zig/issues/19832
    libmicrokit = LazyPath{ .cwd_relative = libmicrokit_opt.? };
    libmicrokit_include = LazyPath{ .cwd_relative = libmicrokit_include_opt.? };
    libmicrokit_linker_script = LazyPath{ .cwd_relative = libmicrokit_linker_script_opt.? };

    // Util libraries
    const util = b.addStaticLibrary(.{
        .name = "util",
        .target = target,
        .optimize = optimize,
    });
    util.addCSourceFiles(.{
        .files = &util_src,
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
    blk_virt.addCSourceFile(.{
        .file = b.path("blk/components/virt.c"),
    });
    blk_virt.addIncludePath(blk_config_include);
    blk_virt.addIncludePath(b.path("include"));
    blk_virt.linkLibrary(util);
    blk_virt.linkLibrary(util_putchar_debug);
    b.installArtifact(blk_virt);

    // Block drivers
    inline for (std.meta.fields(DriverClass.Block)) |class| {
        const driver = addBlockDriver(b, blk_config_include, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }
    inline for (std.meta.fields(DriverClass.Mmc)) |class| {
        const driver = addMmcDriver(b, blk_config_include, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    // Serial components
    const serial_virt_rx = addPd(b, .{
        .name = "serial_virt_rx.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    serial_virt_rx.addCSourceFile(.{
        .file = b.path("serial/components/virt_rx.c"),
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
    });
    i2c_virt.addIncludePath(b.path("include"));
    i2c_virt.linkLibrary(util);
    i2c_virt.linkLibrary(util_putchar_debug);
    b.installArtifact(i2c_virt);

    // I2C drivers
    inline for (std.meta.fields(DriverClass.I2cHost)) |class| {
        const driver = addI2cDriverHost(b, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    inline for (std.meta.fields(DriverClass.I2cDevice)) |device| {
        const driver = addI2cDriverDevice(b, util, @enumFromInt(device.value), target, optimize, i2c_client_include);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    // Network drivers
    inline for (std.meta.fields(DriverClass.Network)) |class| {
        const driver = addNetworkDriver(b, net_config_include, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    // Network components
    const net_virt_rx = addPd(b, .{
        .name = "net_virt_rx.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    net_virt_rx.addCSourceFile(.{
        .file = b.path("network/components/virt_rx.c"),
    });
    net_virt_rx.addIncludePath(net_config_include);
    net_virt_rx.addIncludePath(b.path("include"));
    net_virt_rx.linkLibrary(util);
    net_virt_rx.linkLibrary(util_putchar_debug);
    b.installArtifact(net_virt_rx);

    const net_virt_tx = addPd(b, .{
        .name = "net_virt_tx.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    net_virt_tx.addCSourceFile(.{
        .file = b.path("network/components/virt_tx.c"),
    });
    net_virt_tx.addIncludePath(net_config_include);
    net_virt_tx.addIncludePath(b.path("include"));
    net_virt_tx.linkLibrary(util);
    net_virt_tx.linkLibrary(util_putchar_debug);
    b.installArtifact(net_virt_tx);

    const net_copy = addPd(b, .{
        .name = "net_copy.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    net_copy.addCSourceFile(.{
        .file = b.path("network/components/copy.c"),
    });
    net_copy.addIncludePath(net_config_include);
    net_copy.addIncludePath(b.path("include"));
    net_copy.linkLibrary(util);
    net_copy.linkLibrary(util_putchar_debug);
    b.installArtifact(net_copy);
}
