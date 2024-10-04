/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Copyright (c) 2018 BayLibre, SAS.
 * Author: Jerome Brunet <jbrunet@baylibre.com>
 *
 * Derived from:
 *   https://github.com/torvalds/linux/blob/0c559323bbaabee7346c12e74b497e283aaafef5/drivers/clk/meson/clk-regmap.h
 */

#ifndef SM1_CLK_HWS_H_
#define SM1_CLK_HWS_H_

#include <g12a.h>

#define MESON_FIXED_FACTOR(_name, _mult, _div, _parent_clks, _num_parents, _flags)  \
struct clk _name = {                                                                \
    .data = &(struct clk_fixed_factor_data) {                                       \
        .mult = (_mult),                                                            \
        .div = (_div),                                                              \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_fixed_factor_ops,                                               \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = (_num_parents),                                              \
        .flags = (_flags),                                                          \
    },                                                                              \
}

#define MESON_GATE(_name, _offset, _bit, _data_flags, _parent_clks,                 \
                        _num_parents, _hw_flags)                                    \
struct clk _name = {                                                                \
    .data = &(struct clk_gate_data) {                                               \
        .offset = (_offset),                                                        \
        .bit_idx = (_bit),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_regmap_gate_ops,                                                \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = _num_parents,                                                \
        .flags = (_hw_flags),                                                       \
    },                                                                              \
}

#define MESON_GATE_RO(_name, _offset, _bit, _data_flags, _parent_clks,              \
                        _num_parents, _hw_flags)                                    \
struct clk _name = {                                                                \
    .data = &(struct clk_gate_data) {                                               \
        .offset = (_offset),                                                        \
        .bit_idx = (_bit),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_regmap_gate_ro_ops,                                             \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = _num_parents,                                                \
        .flags = (_hw_flags),                                                       \
    },                                                                              \
}

#define MESON_MUX(_name, _offset, _mask, _shift, _table,                            \
                  _data_flags, _parent_data, _num_parents, _hw_flags)               \
struct clk _name = {                                                                \
    .data = &(struct clk_mux_data) {                                                \
        .offset = (_offset),                                                        \
        .mask = (_mask),                                                            \
        .shift = (_shift),                                                          \
        .table = (_table),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_regmap_mux_ops,                                                 \
        .parent_data = (_parent_data),                                              \
        .num_parents = (_num_parents),                                              \
        .flags = (_hw_flags),                                                       \
    },                                                                              \
}

#define MESON_MUX_RO(_name, _offset, _mask, _shift, _table,                         \
                  _data_flags, _parent_data, _num_parents, _hw_flags)               \
struct clk _name = {                                                                \
    .data = &(struct clk_mux_data) {                                                \
        .offset = (_offset),                                                        \
        .mask = (_mask),                                                            \
        .shift = (_shift),                                                          \
        .table = (_table),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_regmap_mux_ro_ops,                                              \
        .parent_data = (_parent_data),                                              \
        .num_parents = (_num_parents),                                              \
        .flags = (_hw_flags),                                                       \
    },                                                                              \
}

#define MESON_DIV(_name, _offset, _shift, _width, _data_flags,                      \
                  _parent_clks, _num_parents, _hw_flags)                            \
struct clk _name = {                                                                \
    .data = &(struct clk_div_data) {                                                \
        .offset = (_offset),                                                        \
        .shift = (_shift),                                                          \
        .width = (_width),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_regmap_divider_ops,                                             \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = (_num_parents),                                              \
        .flags = (_hw_flags),                                                       \
    },                                                                              \
}

#define MESON_DIV_RO(_name, _offset, _shift, _width, _data_flags,                   \
                  _parent_clks, _num_parents, _hw_flags)                            \
struct clk _name = {                                                                \
    .data = &(struct clk_div_data) {                                                \
        .offset = (_offset),                                                        \
        .shift = (_shift),                                                          \
        .width = (_width),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_regmap_divider_ro_ops,                                          \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = (_num_parents),                                              \
        .flags = (_hw_flags),                                                       \
    },                                                                              \
}

#define MESON_CLK81_GATE(_name, _reg, _bit)                  \
struct clk _name = {                                         \
    .data = &(struct clk_gate_data) {                        \
        .offset = (_reg),                                    \
        .bit_idx = (_bit),                                   \
        .flags = 0,                                          \
    },                                                       \
    .hw.init = &(struct clk_init_data) {                     \
        .name = #_name,                                      \
        .ops = &clk_regmap_gate_ops,                         \
        .parent_clks = (const struct clk *[]) {              \
            &g12a_clk81,                                     \
        },                                                   \
        .num_parents = 1,                                    \
        .flags = 0,                                          \
    },                                                       \
}

#define MESON_CLK81_GATE_RO(_name, _reg, _bit)               \
struct clk _name = {                                         \
    .data = &(struct clk_gate_data) {                        \
        .offset = (_reg),                                    \
        .bit_idx = (_bit),                                   \
        .flags = 0,                                          \
    },                                                       \
    .hw.init = &(struct clk_init_data) {                     \
        .name = #_name,                                      \
        .ops = &clk_regmap_gate_ro_ops,                      \
        .parent_clks = (const struct clk *[]) {              \
            &g12a_clk81,                                     \
        },                                                   \
        .num_parents = 1,                                    \
        .flags = 0,                                          \
    },                                                       \
}

extern const struct clk g12a_xtal;
struct clk **get_clk_list(void);

#endif // SM1_CLK_HWS_H_
