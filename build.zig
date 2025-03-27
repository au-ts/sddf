//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");
const LazyPath = std.Build.LazyPath;

const DriverClass = struct {
    const Serial = enum {
        arm,
        meson,
        imx,
        snps,
        virtio,
    };

    const Timer = enum {
        arm,
        meson,
        imx,
        jh7110,
        goldfish
    };

    const Network = enum {
        imx,
        meson,
        virtio,
        @"dwmac-5.10a",
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

    const Gpu = enum {
        virtio,
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

fn addSerialDriver(
    b: *std.Build,
    util: *std.Build.Step.Compile,
    class: DriverClass.Serial,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
) *std.Build.Step.Compile {
    const driver = addPd(b, .{
        .name = b.fmt("driver_serial_{s}.elf", .{@tagName(class)}),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });

    const source_name = switch (class) {
        .virtio => "console.c",
        else => "uart.c",
    };
    const source = b.fmt("drivers/serial/{s}/{s}", .{@tagName(class), source_name});
    const driver_include = b.fmt("drivers/serial/{s}/include", .{@tagName(class)});
    driver.addCSourceFile(.{
        .file = b.path(source),
    });
    driver.addIncludePath(b.path("include"));
    driver.addIncludePath(b.path("include/microkit"));
    driver.addIncludePath(b.path(driver_include));
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
    driver.addIncludePath(b.path("include/microkit"));
    driver.linkLibrary(util);

    return driver;
}

fn addI2cDriverDevice(
    b: *std.Build,
    util: *std.Build.Step.Compile,
    device: DriverClass.I2cDevice,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
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
    driver.addIncludePath(b.path("include/microkit"));
    driver.linkLibrary(util);
    driver.addIncludePath(b.path("libco"));

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
    driver.addIncludePath(b.path("include/microkit"));
    driver.linkLibrary(util);

    return driver;
}

fn addBlockDriver(
    b: *std.Build,
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
    driver.addIncludePath(b.path(b.fmt("drivers/blk/{s}/", .{ @tagName(class) })));
    driver.addIncludePath(b.path("include"));
    driver.addIncludePath(b.path("include/microkit"));
    driver.linkLibrary(util);

    return driver;
}

fn addMmcDriver(
    b: *std.Build,
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
    driver.addIncludePath(b.path(b.fmt("drivers/blk/mmc/{s}/", .{ @tagName(class) })));
    driver.addIncludePath(b.path("include"));
    driver.addIncludePath(b.path("include/microkit"));
    driver.linkLibrary(util);

    return driver;
}

fn addNetworkDriver(
    b: *std.Build,
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
    driver.addIncludePath(b.path(b.fmt("drivers/network/{s}/", .{ @tagName(class) })));
    driver.addIncludePath(b.path("include"));
    driver.addIncludePath(b.path("include/microkit"));
    driver.linkLibrary(util);

    return driver;
}

fn addGpuDriver(
    b: *std.Build,
    gpu_config_include: LazyPath,
    util: *std.Build.Step.Compile,
    class: DriverClass.Gpu,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
) *std.Build.Step.Compile {
    const driver = addPd(b, .{
        .name = b.fmt("driver_gpu_{s}.elf", .{ @tagName(class) }),
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    const source = b.fmt("drivers/gpu/{s}/gpu.c", .{ @tagName(class) });
    driver.addCSourceFile(.{
        .file = b.path(source),
    });
    driver.addIncludePath(gpu_config_include);
    driver.addIncludePath(b.path(b.fmt("drivers/gpu/{s}/", .{ @tagName(class) })));
    driver.addIncludePath(b.path("include"));
    driver.addIncludePath(b.path("include/microkit"));
    driver.linkLibrary(util);

    return driver;
}

fn addPd(b: *std.Build, options: std.Build.ExecutableOptions) *std.Build.Step.Compile {
    const pd = b.addExecutable(options);
    pd.addObjectFile(libmicrokit);
    pd.setLinkerScript(libmicrokit_linker_script);
    pd.addIncludePath(libmicrokit_include);

    return pd;
}

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    const libmicrokit_opt = b.option([]const u8, "libmicrokit", "Path to libmicrokit.a") orelse null;
    const libmicrokit_include_opt = b.option([]const u8, "libmicrokit_include", "Path to the libmicrokit include directory") orelse null;
    const libmicrokit_linker_script_opt = b.option([]const u8, "libmicrokit_linker_script", "Path to the libmicrokit linker script") orelse null;
    const gpu_config_include_option = b.option([]const u8, "gpu_config_include", "Include path to gpu config header") orelse "";

    // TODO: Right now this is not super ideal. What's happening is that we do not
    // always need a serial config include, but we must always specify it
    // as a build option. What we do instead is just make the include path an
    // empty string if it has not been provided, which could be an annoying to
    // debug error if you do need a serial config but forgot to pass one in.
    const gpu_config_include = LazyPath{ .cwd_relative = gpu_config_include_option };
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
    util.addIncludePath(b.path("include/microkit"));
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
    util_putchar_serial.addIncludePath(b.path("include/microkit"));
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
    util_putchar_debug.addIncludePath(b.path("include/microkit"));
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
    blk_virt.addCSourceFiles(.{
        .files = &. { "blk/components/virt.c", "blk/components/partitioning.c" },
    });
    blk_virt.addIncludePath(b.path("include"));
    blk_virt.addIncludePath(b.path("include/microkit"));
    blk_virt.linkLibrary(util);
    blk_virt.linkLibrary(util_putchar_debug);
    b.installArtifact(blk_virt);

    // Block drivers
    inline for (std.meta.fields(DriverClass.Block)) |class| {
        const driver = addBlockDriver(b, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }
    inline for (std.meta.fields(DriverClass.Mmc)) |class| {
        const driver = addMmcDriver(b, util, @enumFromInt(class.value), target, optimize);
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
    serial_virt_rx.addIncludePath(b.path("include"));
    serial_virt_rx.addIncludePath(b.path("include/microkit"));
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
    serial_virt_tx.addIncludePath(b.path("include"));
    serial_virt_tx.addIncludePath(b.path("include/microkit"));
    serial_virt_tx.linkLibrary(util);
    serial_virt_tx.linkLibrary(util_putchar_debug);
    b.installArtifact(serial_virt_tx);

    // Serial drivers
    inline for (std.meta.fields(DriverClass.Serial)) |class| {
        const driver = addSerialDriver(b, util, @enumFromInt(class.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    // Gpu components
    const gpu_virt = addPd(b, .{
        .name = "gpu_virt.elf",
        .target = target,
        .optimize = optimize,
        .strip = false,
    });
    gpu_virt.addCSourceFile(.{
        .file = b.path("gpu/components/virt.c"),
    });
    gpu_virt.addIncludePath(gpu_config_include);
    gpu_virt.addIncludePath(b.path("include"));
    gpu_virt.addIncludePath(b.path("include/microkit"));
    gpu_virt.linkLibrary(util);
    gpu_virt.linkLibrary(util_putchar_debug);
    b.installArtifact(gpu_virt);

    // Gpu drivers
    inline for (std.meta.fields(DriverClass.Gpu)) |class| {
        const driver = addGpuDriver(b, gpu_config_include, util, @enumFromInt(class.value), target, optimize);
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
    i2c_virt.addIncludePath(b.path("include/microkit"));
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
        const driver = addI2cDriverDevice(b, util, @enumFromInt(device.value), target, optimize);
        driver.linkLibrary(util_putchar_debug);
        b.installArtifact(driver);
    }

    // Network drivers
    inline for (std.meta.fields(DriverClass.Network)) |class| {
        const driver = addNetworkDriver(b, util, @enumFromInt(class.value), target, optimize);
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
    net_virt_rx.addIncludePath(b.path("include"));
    net_virt_rx.addIncludePath(b.path("include/microkit"));
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
    net_virt_tx.addIncludePath(b.path("include"));
    net_virt_tx.addIncludePath(b.path("include/microkit"));
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
    net_copy.addIncludePath(b.path("include"));
    net_copy.addIncludePath(b.path("include/microkit"));
    net_copy.linkLibrary(util);
    net_copy.linkLibrary(util_putchar_debug);
    b.installArtifact(net_copy);
}
