/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <clk.h>

#define CLK_INCORRECT_ARGS 1
#define CLK_INVALID_OP 2

int reg_write(uint64_t base, uint32_t offset, uint32_t val);
int regmap_update_bits(uint64_t base, uint32_t offset, uint8_t shift, uint8_t width, uint32_t val);
int regmap_read_bits(uint64_t base, uint32_t offset, uint8_t shift, uint8_t width);
int regmap_mux_update_bits(uint64_t base, uint32_t offset, uint8_t shift, uint32_t mask, uint32_t val);
int regmap_mux_read_bits(uint64_t base, uint32_t offset, uint8_t shift, uint32_t mask);

extern const struct clk_ops clk_source_ops;
extern const struct clk_ops clk_fixed_factor_ops;
extern const struct clk_ops clk_divider_ops;
extern const struct clk_ops clk_divider_ro_ops;
extern const struct clk_ops clk_mux_ops;
extern const struct clk_ops clk_mux_ro_ops;
extern const struct clk_ops clk_gate_ops;
extern const struct clk_ops clk_gate_ro_ops;

#define CLK_FIXED_FACTOR(_name, _mult, _div, _data_flags, _parent_clks,             \
                         _num_parents, _init_flags)                                 \
struct clk _name = {                                                                \
    .data = &(struct clk_fixed_factor_data) {                                       \
        .mult = (_mult),                                                            \
        .div = (_div),                                                              \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_fixed_factor_ops,                                               \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = (_num_parents),                                              \
        .flags = (_init_flags),                                                     \
    },                                                                              \
}

#define CLK_GATE(_name, _offset, _bit, _data_flags, _parent_clks,                   \
                        _num_parents, _init_flags)                                  \
struct clk _name = {                                                                \
    .data = &(struct clk_gate_data) {                                               \
        .offset = (_offset),                                                        \
        .bit_idx = (_bit),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_gate_ops,                                                       \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = _num_parents,                                                \
        .flags = (_init_flags),                                                     \
    },                                                                              \
}

#define CLK_GATE_RO(_name, _offset, _bit, _data_flags, _parent_clks,                \
                        _num_parents, _init_flags)                                  \
struct clk _name = {                                                                \
    .data = &(struct clk_gate_data) {                                               \
        .offset = (_offset),                                                        \
        .bit_idx = (_bit),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_gate_ro_ops,                                                    \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = _num_parents,                                                \
        .flags = (_init_flags),                                                     \
    },                                                                              \
}

#define CLK_MUX(_name, _offset, _mask, _shift, _table,                              \
                  _data_flags, _parent_data, _num_parents, _init_flags)             \
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
        .ops = &clk_mux_ops,                                                        \
        .parent_data = (_parent_data),                                              \
        .num_parents = (_num_parents),                                              \
        .flags = (_init_flags),                                                     \
    },                                                                              \
}

#define CLK_MUX_RO(_name, _offset, _mask, _shift, _table,                           \
                  _data_flags, _parent_data, _num_parents, _init_flags)             \
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
        .ops = &clk_mux_ro_ops,                                                     \
        .parent_data = (_parent_data),                                              \
        .num_parents = (_num_parents),                                              \
        .flags = (_init_flags),                                                     \
    },                                                                              \
}

#define CLK_DIV(_name, _offset, _shift, _width, _data_flags,                        \
                  _parent_clks, _num_parents, _init_flags)                          \
struct clk _name = {                                                                \
    .data = &(struct clk_div_data) {                                                \
        .offset = (_offset),                                                        \
        .shift = (_shift),                                                          \
        .width = (_width),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_divider_ops,                                                    \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = (_num_parents),                                              \
        .flags = (_init_flags),                                                     \
    },                                                                              \
}

#define CLK_DIV_RO(_name, _offset, _shift, _width, _data_flags,                     \
                  _parent_clks, _num_parents, _init_flags)                          \
struct clk _name = {                                                                \
    .data = &(struct clk_div_data) {                                                \
        .offset = (_offset),                                                        \
        .shift = (_shift),                                                          \
        .width = (_width),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_divider_ro_ops,                                                 \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = (_num_parents),                                              \
        .flags = (_init_flags),                                                     \
    },                                                                              \
}