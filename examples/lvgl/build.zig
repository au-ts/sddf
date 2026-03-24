//
// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause
//
const std = @import("std");
const LazyPath = std.Build.LazyPath;
const Step = std.Build.Step;

const MicrokitBoard = enum {
    qemu_virt_aarch64,
    qemu_virt_riscv64,
    odroidc2,
    odroidc4,
    star64,
    serengeti,
    maaxboard,
    imx8mm_evk,
    imx8mp_evk,
    imx8mq_evk,
    zcu102,
    rock3b,
    rpi4b_1gb,
    x86_64_generic,
};

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
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{.strict_align}),
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
        },
    },
    .{
        .board = MicrokitBoard.odroidc2,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{.strict_align}),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
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
    .{
        .board = MicrokitBoard.imx8mm_evk,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{.strict_align}),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.imx8mp_evk,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{.strict_align}),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.imx8mq_evk,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{.strict_align}),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.serengeti,
        .zig_target = std.Target.Query{
            .cpu_arch = .riscv64,
            .cpu_model = .{ .explicit = &std.Target.riscv.cpu.baseline_rv64 },
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
        },
    },
    .{
        .board = MicrokitBoard.zcu102,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a53 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{.strict_align}),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.rpi4b_1gb,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a72 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{.strict_align}),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.rock3b,
        .zig_target = std.Target.Query{
            .cpu_arch = .aarch64,
            .cpu_model = .{ .explicit = &std.Target.aarch64.cpu.cortex_a55 },
            .cpu_features_add = std.Target.aarch64.featureSet(&[_]std.Target.aarch64.Feature{.strict_align}),
            .os_tag = .freestanding,
            .abi = .none,
        },
    },
    .{
        .board = MicrokitBoard.x86_64_generic,
        .zig_target = std.Target.Query{
            .cpu_arch = .x86_64,
            .cpu_model = .{ .explicit = std.Target.Cpu.Model.generic(.x86_64) },
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
    });

    const driver_class = switch (microkit_board_option) {
        .qemu_virt_aarch64 => "arm",
        .qemu_virt_riscv64 => "goldfish",
        .odroidc2, .odroidc4 => "meson",
        .star64 => "jh7110",
        .serengeti => "apb_timer",
        .maaxboard, .imx8mm_evk, .imx8mp_evk, .imx8mq_evk => "imx",
        .zcu102 => "cdns",
        .rock3b => "rk3568",
        .rpi4b_1gb => "bcm2835",
        .x86_64_generic => "hpet",
    };

    const driver = sddf_dep.artifact(b.fmt("driver_timer_{s}.elf", .{driver_class}));
    // This is required because the SDF file is expecting a different name to the artifact we
    // are dealing with.
    const driver_install = b.addInstallArtifact(driver, .{ .dest_sub_path = "timer_driver.elf" });

    const client = b.addExecutable(.{
        .name = "client.elf",
        .root_module = b.createModule(.{
            .target = target,
            .optimize = optimize,
            .strip = false,
        }),
    });

    const lvgl_core = &.{
        "lvgl/src/core/lv_group.c",
        "lvgl/src/core/lv_obj.c",
        "lvgl/src/core/lv_obj_class.c",
        "lvgl/src/core/lv_obj_draw.c",
        "lvgl/src/core/lv_obj_event.c",
        "lvgl/src/core/lv_obj_id_builtin.c",
        "lvgl/src/core/lv_obj_pos.c",
        "lvgl/src/core/lv_obj_property.c",
        "lvgl/src/core/lv_obj_scroll.c",
        "lvgl/src/core/lv_obj_style.c",
        "lvgl/src/core/lv_obj_style_gen.c",
        "lvgl/src/core/lv_obj_tree.c",
        "lvgl/src/core/lv_observer.c",
        "lvgl/src/core/lv_refr.c",
    };

    const lvgl_draw = &.{
        "lvgl/src/draw/lv_draw.c",
        "lvgl/src/draw/lv_draw_3d.c",
        "lvgl/src/draw/lv_draw_arc.c",
        "lvgl/src/draw/lv_draw_blur.c",
        "lvgl/src/draw/lv_draw_buf.c",
        "lvgl/src/draw/lv_draw_image.c",
        "lvgl/src/draw/lv_draw_label.c",
        "lvgl/src/draw/lv_draw_line.c",
        "lvgl/src/draw/lv_draw_mask.c",
        "lvgl/src/draw/lv_draw_rect.c",
        "lvgl/src/draw/lv_draw_triangle.c",
        "lvgl/src/draw/lv_draw_vector.c",
        "lvgl/src/draw/lv_image_decoder.c",
        "lvgl/src/draw/convert/helium/lv_draw_buf_convert_helium.c",
        "lvgl/src/draw/convert/lv_draw_buf_convert.c",
        "lvgl/src/draw/convert/neon/lv_draw_buf_convert_neon.c",
        "lvgl/src/draw/sw/lv_draw_sw.c",
        "lvgl/src/draw/sw/lv_draw_sw_arc.c",
        "lvgl/src/draw/sw/lv_draw_sw_blur.c",
        "lvgl/src/draw/sw/lv_draw_sw_border.c",
        "lvgl/src/draw/sw/lv_draw_sw_box_shadow.c",
        "lvgl/src/draw/sw/lv_draw_sw_fill.c",
        "lvgl/src/draw/sw/lv_draw_sw_grad.c",
        "lvgl/src/draw/sw/lv_draw_sw_img.c",
        "lvgl/src/draw/sw/lv_draw_sw_letter.c",
        "lvgl/src/draw/sw/lv_draw_sw_line.c",
        "lvgl/src/draw/sw/lv_draw_sw_mask.c",
        "lvgl/src/draw/sw/lv_draw_sw_mask_rect.c",
        "lvgl/src/draw/sw/lv_draw_sw_transform.c",
        "lvgl/src/draw/sw/lv_draw_sw_triangle.c",
        "lvgl/src/draw/sw/lv_draw_sw_utils.c",
        "lvgl/src/draw/sw/lv_draw_sw_vector.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend_to_a8.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend_to_al88.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend_to_argb8888.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend_to_argb8888_premultiplied.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend_to_i1.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend_to_l8.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend_to_rgb565.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend_to_rgb565_swapped.c",
        "lvgl/src/draw/sw/blend/lv_draw_sw_blend_to_rgb888.c",
    };

    const lvgl_misc = &.{
        "lvgl/src/misc/lv_anim.c",
        "lvgl/src/misc/lv_anim_timeline.c",
        "lvgl/src/misc/lv_area.c",
        "lvgl/src/misc/lv_array.c",
        "lvgl/src/misc/lv_async.c",
        "lvgl/src/misc/lv_bidi.c",
        "lvgl/src/misc/lv_circle_buf.c",
        "lvgl/src/misc/lv_color.c",
        "lvgl/src/misc/lv_color_op.c",
        "lvgl/src/misc/lv_event.c",
        "lvgl/src/misc/lv_fs.c",
        "lvgl/src/misc/lv_grad.c",
        "lvgl/src/misc/lv_iter.c",
        "lvgl/src/misc/lv_ll.c",
        "lvgl/src/misc/lv_log.c",
        "lvgl/src/misc/lv_lru.c",
        "lvgl/src/misc/lv_math.c",
        "lvgl/src/misc/lv_matrix.c",
        "lvgl/src/misc/lv_palette.c",
        "lvgl/src/misc/lv_pending.c",
        "lvgl/src/misc/lv_rb.c",
        "lvgl/src/misc/lv_style.c",
        "lvgl/src/misc/lv_style_gen.c",
        "lvgl/src/misc/lv_templ.c",
        "lvgl/src/misc/lv_text.c",
        "lvgl/src/misc/lv_text_ap.c",
        "lvgl/src/misc/lv_timer.c",
        "lvgl/src/misc/lv_tree.c",
        "lvgl/src/misc/lv_utils.c",
        "lvgl/src/misc/cache/lv_cache.c",
        "lvgl/src/misc/cache/lv_cache_entry.c",
        "lvgl/src/misc/cache/class/lv_cache_lru_rb.c",
        "lvgl/src/misc/cache/instance/lv_image_cache.c",
        "lvgl/src/misc/cache/instance/lv_image_header_cache.c",
    };

    const lvgl_fonts = &.{
        "lvgl/src/font/binfont_loader/lv_binfont_loader.c",
        "lvgl/src/font/fmt_txt/lv_font_fmt_txt.c",
        "lvgl/src/font/font_manager/lv_font_manager.c",
        "lvgl/src/font/font_manager/lv_font_manager_recycle.c",
        "lvgl/src/font/imgfont/lv_imgfont.c",
        "lvgl/src/font/lv_font.c",
        "lvgl/src/font/lv_font_dejavu_16_persian_hebrew.c",
        "lvgl/src/font/lv_font_montserrat_10.c",
        "lvgl/src/font/lv_font_montserrat_12.c",
        "lvgl/src/font/lv_font_montserrat_14.c",
        "lvgl/src/font/lv_font_montserrat_14_aligned.c",
        "lvgl/src/font/lv_font_montserrat_16.c",
        "lvgl/src/font/lv_font_montserrat_18.c",
        "lvgl/src/font/lv_font_montserrat_20.c",
        "lvgl/src/font/lv_font_montserrat_22.c",
        "lvgl/src/font/lv_font_montserrat_24.c",
        "lvgl/src/font/lv_font_montserrat_26.c",
        "lvgl/src/font/lv_font_montserrat_28.c",
        "lvgl/src/font/lv_font_montserrat_28_compressed.c",
        "lvgl/src/font/lv_font_montserrat_30.c",
        "lvgl/src/font/lv_font_montserrat_32.c",
        "lvgl/src/font/lv_font_montserrat_34.c",
        "lvgl/src/font/lv_font_montserrat_36.c",
        "lvgl/src/font/lv_font_montserrat_38.c",
        "lvgl/src/font/lv_font_montserrat_40.c",
        "lvgl/src/font/lv_font_montserrat_42.c",
        "lvgl/src/font/lv_font_montserrat_44.c",
        "lvgl/src/font/lv_font_montserrat_46.c",
        "lvgl/src/font/lv_font_montserrat_48.c",
        "lvgl/src/font/lv_font_montserrat_8.c",
        "lvgl/src/font/lv_font_source_han_sans_sc_14_cjk.c",
        "lvgl/src/font/lv_font_source_han_sans_sc_16_cjk.c",
        "lvgl/src/font/lv_font_unscii_16.c",
        "lvgl/src/font/lv_font_unscii_8.c",
    };

    const lvgl_widgets = &.{
        "lvgl/src/widgets/arc/lv_arc.c",
        "lvgl/src/widgets/arclabel/lv_arclabel.c",
        "lvgl/src/widgets/bar/lv_bar.c",
        "lvgl/src/widgets/button/lv_button.c",
        "lvgl/src/widgets/buttonmatrix/lv_buttonmatrix.c",
        "lvgl/src/widgets/calendar/lv_calendar.c",
        "lvgl/src/widgets/calendar/lv_calendar_chinese.c",
        "lvgl/src/widgets/calendar/lv_calendar_header_arrow.c",
        "lvgl/src/widgets/calendar/lv_calendar_header_dropdown.c",
        "lvgl/src/widgets/canvas/lv_canvas.c",
        "lvgl/src/widgets/chart/lv_chart.c",
        "lvgl/src/widgets/checkbox/lv_checkbox.c",
        "lvgl/src/widgets/dropdown/lv_dropdown.c",
        "lvgl/src/widgets/gif/lv_gif.c",
        "lvgl/src/widgets/image/lv_image.c",
        "lvgl/src/widgets/imagebutton/lv_imagebutton.c",
        "lvgl/src/widgets/ime/lv_ime_pinyin.c",
        "lvgl/src/widgets/keyboard/lv_keyboard.c",
        "lvgl/src/widgets/label/lv_label.c",
        "lvgl/src/widgets/led/lv_led.c",
        "lvgl/src/widgets/line/lv_line.c",
        "lvgl/src/widgets/list/lv_list.c",
        "lvgl/src/widgets/lottie/lv_lottie.c",
        "lvgl/src/widgets/menu/lv_menu.c",
        "lvgl/src/widgets/msgbox/lv_msgbox.c",
        "lvgl/src/widgets/objx_templ/lv_objx_templ.c",
        "lvgl/src/widgets/property/lv_animimage_properties.c",
        "lvgl/src/widgets/property/lv_arc_properties.c",
        "lvgl/src/widgets/property/lv_bar_properties.c",
        "lvgl/src/widgets/property/lv_buttonmatrix_properties.c",
        "lvgl/src/widgets/property/lv_chart_properties.c",
        "lvgl/src/widgets/property/lv_checkbox_properties.c",
        "lvgl/src/widgets/property/lv_dropdown_properties.c",
        "lvgl/src/widgets/property/lv_image_properties.c",
        "lvgl/src/widgets/property/lv_keyboard_properties.c",
        "lvgl/src/widgets/property/lv_label_properties.c",
        "lvgl/src/widgets/property/lv_led_properties.c",
        "lvgl/src/widgets/property/lv_line_properties.c",
        "lvgl/src/widgets/property/lv_menu_properties.c",
        "lvgl/src/widgets/property/lv_obj_properties.c",
        "lvgl/src/widgets/property/lv_roller_properties.c",
        "lvgl/src/widgets/property/lv_scale_properties.c",
        "lvgl/src/widgets/property/lv_slider_properties.c",
        "lvgl/src/widgets/property/lv_span_properties.c",
        "lvgl/src/widgets/property/lv_spinbox_properties.c",
        "lvgl/src/widgets/property/lv_spinner_properties.c",
        "lvgl/src/widgets/property/lv_style_properties.c",
        "lvgl/src/widgets/property/lv_switch_properties.c",
        "lvgl/src/widgets/property/lv_table_properties.c",
        "lvgl/src/widgets/property/lv_tabview_properties.c",
        "lvgl/src/widgets/property/lv_textarea_properties.c",
        "lvgl/src/widgets/roller/lv_roller.c",
        "lvgl/src/widgets/scale/lv_scale.c",
        "lvgl/src/widgets/slider/lv_slider.c",
        "lvgl/src/widgets/span/lv_span.c",
        "lvgl/src/widgets/spinbox/lv_spinbox.c",
        "lvgl/src/widgets/spinner/lv_spinner.c",
        "lvgl/src/widgets/switch/lv_switch.c",
        "lvgl/src/widgets/table/lv_table.c",
        "lvgl/src/widgets/tabview/lv_tabview.c",
        "lvgl/src/widgets/textarea/lv_textarea.c",
        "lvgl/src/widgets/tileview/lv_tileview.c",
        "lvgl/src/widgets/win/lv_win.c",
    };

    const lvgl_builtin = &.{
        "lvgl/src/stdlib/builtin/lv_mem_core_builtin.c",
        "lvgl/src/stdlib/builtin/lv_sprintf_builtin.c",
        "lvgl/src/stdlib/builtin/lv_string_builtin.c",
        "lvgl/src/stdlib/builtin/lv_tlsf.c",
        "lvgl/src/stdlib/lv_mem.c",
    };

    const lvgl = &.{
        "lvgl/src/display/lv_display.c",
        "lvgl/src/themes/lv_theme.c",
        "lvgl/src/themes/mono/lv_theme_mono.c",
        "lvgl/src/themes/default/lv_theme_default.c",
        "lvgl/src/themes/simple/lv_theme_simple.c",
        "lvgl/src/layouts/flex/lv_flex.c",
        "lvgl/src/layouts/grid/lv_grid.c",
        "lvgl/src/layouts/lv_layout.c",
        "lvgl/src/indev/lv_indev.c",
        "lvgl/src/indev/lv_indev_scroll.c",
        "lvgl/src/lv_init.c",
        "lvgl/src/tick/lv_tick.c",
        "lvgl/src/osal/lv_os.c",
        "lvgl/src/libs/bin_decoder/lv_bin_decoder.c",
    };
    inline for (lvgl) |file| {
        client.addCSourceFile(.{ .file = b.path(file) });
    }
    inline for (lvgl_builtin) |file| {
        client.addCSourceFile(.{ .file = b.path(file) });
    }
    inline for (lvgl_fonts) |file| {
        client.addCSourceFile(.{ .file = b.path(file) });
    }
    inline for (lvgl_widgets) |file| {
        client.addCSourceFile(.{ .file = b.path(file) });
    }
    inline for (lvgl_core) |file| {
        client.addCSourceFile(.{ .file = b.path(file) });
    }
    inline for (lvgl_draw) |file| {
        client.addCSourceFile(.{ .file = b.path(file) });
    }
    inline for (lvgl_misc) |file| {
        client.addCSourceFile(.{ .file = b.path(file) });
    }
    client.addIncludePath(b.path(""));
    client.addIncludePath(b.path("lvgl"));
    client.addIncludePath(b.path("lvgl/src/stdlib"));

    client.addCSourceFile(.{ .file = b.path("client.c") });
    client.addCSourceFile(.{ .file = b.path("ramfb.c") });
    client.addIncludePath(sddf_dep.path("include"));
    client.addIncludePath(sddf_dep.path("include/microkit"));
    client.linkLibrary(sddf_dep.artifact("util"));
    client.linkLibrary(sddf_dep.artifact("util_putchar_debug"));

    client.addIncludePath(libmicrokit_include);
    client.addObjectFile(libmicrokit);
    client.setLinkerScript(libmicrokit_linker_script);

    b.installArtifact(client);

    const virtio_input_driver = sddf_dep.artifact(b.fmt("driver_input_{s}.elf", .{"virtio"}));
    const keyboard_driver_install = b.addInstallArtifact(virtio_input_driver, .{ .dest_sub_path = "virtio_keyboard_driver.elf" });
    const mouse_driver_install = b.addInstallArtifact(virtio_input_driver, .{ .dest_sub_path = "virtio_mouse_driver.elf" });

    const dtb = blk: {
        if (target.result.cpu.arch != .x86_64) {
            // For compiling the DTS into a DTB
            const dts = sddf_dep.path(b.fmt("dts/{s}.dts", .{microkit_board}));
            const dtc_cmd = b.addSystemCommand(&[_][]const u8{ "dtc", "-q", "-I", "dts", "-O", "dtb" });
            dtc_cmd.addFileInput(dts);
            dtc_cmd.addFileArg(dts);
            break :blk dtc_cmd.captureStdOut();
        } else {
            break :blk null;
        }
    };
    // Run the metaprogram to get sDDF configuration binary files and the SDF file.
    const metaprogram = b.path("meta.py");
    const run_metaprogram = b.addSystemCommand(&[_][]const u8{
        python,
    });
    run_metaprogram.addFileArg(metaprogram);
    run_metaprogram.addFileInput(metaprogram);
    run_metaprogram.addPrefixedDirectoryArg("--sddf=", sddf_dep.path(""));
    if (dtb != null) {
        run_metaprogram.addPrefixedDirectoryArg("--dtb=", dtb.?);
    }
    const meta_output = run_metaprogram.addPrefixedOutputDirectoryArg("--output=", "meta_output");
    run_metaprogram.addArg("--board");
    run_metaprogram.addArg(microkit_board);
    run_metaprogram.addArg("--sdf");
    run_metaprogram.addArg("timer.system");

    const meta_output_install = b.addInstallDirectory(.{
        .source_dir = meta_output,
        .install_dir = .prefix,
        .install_subdir = "meta_output",
    });

    const client_objcopy = updateSectionObjcopy(b, ".timer_client_config", meta_output, "timer_client_client.data", "client.elf");
    const driver_objcopy = updateSectionObjcopy(b, ".device_resources", meta_output, "timer_driver_device_resources.data", "timer_driver.elf");
    driver_objcopy.step.dependOn(&driver_install.step);
    const objcopys = &.{ client_objcopy, driver_objcopy };

    const final_image_dest = b.getInstallPath(.bin, "./loader.img");
    const microkit_tool_cmd = Step.Run.create(b, "run microkit tool");
    microkit_tool_cmd.addFileArg(microkit_tool);
    microkit_tool_cmd.addArgs(&[_][]const u8{
        b.getInstallPath(.{ .custom = "meta_output" }, "timer.system"),
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
    microkit_tool_cmd.step.dependOn(&keyboard_driver_install.step);
    microkit_tool_cmd.step.dependOn(&mouse_driver_install.step);
    microkit_tool_cmd.step.dependOn(&meta_output_install.step);
    microkit_tool_cmd.step.dependOn(b.getInstallStep());
    microkit_tool_cmd.setEnvironmentVariable("MICROKIT_SDK", microkit_sdk.getPath3(b, null).toString(b.allocator) catch @panic("OOM"));

    const microkit_step = b.step("microkit", "Compile and build the final bootable image");
    microkit_step.dependOn(&microkit_tool_cmd.step);
    b.default_step = microkit_step;

    // This is setting up a `qemu` command for running the system using QEMU,
    // which we only want to do when we have a board that we can actually simulate.
    var qemu_cmd: ?*Step.Run = null;
    if (microkit_board_option == .qemu_virt_aarch64) {
        const loader_arg = b.fmt("loader,file={s},addr=0x70000000,cpu-num=0", .{final_image_dest});
        qemu_cmd = b.addSystemCommand(&[_][]const u8{
            "qemu-system-aarch64",
            "-machine",
            "virt,virtualization=on",
            "-cpu",
            "cortex-a53",
            "-serial",
            "mon:stdio",
            "-device",
            loader_arg,
            "-m",
            "2G",
            "-device", "ramfb",
            "-device", "virtio-keyboard-device",
            "-device", "virtio-tablet-device",
            "-global", "virtio-mmio.force-legacy=false",
        });
    } else if (microkit_board_option == .qemu_virt_riscv64) {
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
    } else if (microkit_board_option == .x86_64_generic) {
        const kernel_32 = microkit_board_dir.path(b, "elf/sel4_32.elf");
        qemu_cmd = b.addSystemCommand(&[_][]const u8{
            "qemu-system-x86_64",
            "-machine",
            "q35",
            "-cpu",
            "qemu64,+fsgsbase,+pdpe1gb,+pcid,+invpcid,+xsave,+xsaves,+xsaveopt",
            "-serial",
            "mon:stdio",
            "-kernel",
            b.getInstallPath(.bin, "sel4_32.elf"),
            "-initrd",
            final_image_dest,
            "-m",
            "2G",
            "-nographic",
        });
        qemu_cmd.?.step.dependOn(&b.addInstallFileWithDir(kernel_32, .bin, "sel4_32.elf").step);
    }

    if (qemu_cmd) |cmd| {
        cmd.step.dependOn(b.default_step);
        const simulate_step = b.step("qemu", "Simulate the image using QEMU");
        simulate_step.dependOn(&cmd.step);
    }
}
