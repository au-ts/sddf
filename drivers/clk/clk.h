#ifndef CLK_H_
#define CLK_H_

#include <stdint.h>

#define TEST_VAL 1

#define CLK_SOURCE(_name, _rate)                                                    \
struct clk _name = {                                                                \
    .data = &(struct clk_source_data) {                                             \
        .rate = (_rate),                                                            \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_source_ops,                                                     \
    },                                                                              \
}

#define CLK_FIXED_FACTOR(_name, _mult, _div, _parent_clks, _num_parents, _flags)    \
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

#define CLK_GATE(_name, _offset, _bit, _data_flags, _parent_clks,                   \
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

#define CLK_GATE_RO(_name, _offset, _bit, _data_flags, _parent_clks,                \
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

#define CLK_MUX(_name, _offset, _mask, _shift, _table,                           \
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

#define CLK_MUX_RO(_name, _offset, _mask, _shift, _table,                        \
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

#define CLK_DIV(_name, _offset, _shift, _width, _data_flags,                     \
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

#define CLK_DIV_RO(_name, _offset, _shift, _width, _data_flags,                   \
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

#endif // CLK_H_
