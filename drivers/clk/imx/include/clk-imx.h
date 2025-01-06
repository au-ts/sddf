// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2010-2011 Canonical Ltd <jeremy.kerr@canonical.com>
 * Copyright (C) 2011-2012 Mike Turquette, Linaro Ltd <mturquette@linaro.org>
 *
 * Gated clock implementation
 * Source: https://github.com/torvalds/linux/blob/
 *   cfaaa7d010d1fc58f9717fcc8591201e741d2d49/drivers/clk/imx/clk-gate2.c
 */

// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright 2018 NXP.
 *
 * Source: https://github.com/torvalds/linux/blob/
 *   cfaaa7d010d1fc58f9717fcc8591201e741d2d49/drivers/clk/imx/clk-frac-pll.c
 */

// SPDX-License-Identifier: GPL-2.0-only OR MIT
/*
 * Copyright 2018 NXP.
 *
 * Source: https://github.com/torvalds/linux/blob/
 *   cfaaa7d010d1fc58f9717fcc8591201e741d2d49/drivers/clk/imx/clk-sscg-pll.c
 */

// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright 2018 NXP
 *
 * Source: https://github.com/torvalds/linux/blob/
 *   cfaaa7d010d1fc58f9717fcc8591201e741d2d49/drivers/clk/imx/clk-composite-8m.c
 */
#pragma once

#include <stdint.h>

/* These two magic numbers are used to define static clock
 * structures at compile time, and will be replaced with
 * real base addresses in clk_probe().
 */
#define CCM_BASE 0x1234
#define CCM_ANALOG_BASE 0x5678

#define PCG_PREDIV_SHIFT    16
#define PCG_PREDIV_WIDTH    3
#define PCG_PREDIV_MAX      8

#define PCG_DIV_SHIFT       0
#define PCG_CORE_DIV_WIDTH  3
#define PCG_DIV_WIDTH       6
#define PCG_DIV_MAX         64

#define PCG_PCS_SHIFT       24
#define PCG_PCS_MASK        0x7

#define PCG_CGC_SHIFT       28

struct clk_gate2 {
    uint8_t bit_idx;
    uint8_t cgr_val;
    uint8_t cgr_mask;
    uint8_t flags;
    uint32_t *share_count;
};

struct clk_frac_pll_data {
    uint32_t offset;
};

struct clk_sscg_pll_data {
    /* struct clk_sscg_pll_setup setup; */
    uint32_t offset;
    uint8_t parent;
    uint8_t bypass1;
    uint8_t bypass2;
};

/**
 * Refer to section 5.1.5.4.1 Core clock slice in datasheet.
 */
struct clk_core_slice_data {
    /* Common */
    uint32_t offset;
    /* Mux */
    uint8_t mux_shift;
    uint8_t mux_mask;
    /* Gate */
    uint8_t gate_shift;
    /* Divider */
    uint8_t div_shift;
    uint8_t div_width;
};

/**
 * Refer to section 5.1.5.4.2 Bus clock slice in datasheet.
 */
struct clk_bus_slice_data {
    /* Common */
    uint32_t offset;
    /* Mux */
    uint8_t mux_shift;
    uint8_t mux_mask;
    /* Gate */
    uint8_t gate_shift;
    /* Prev Divider */
    uint8_t prevdiv_shift;
    uint8_t prevdiv_width;
    /* Post Divider */
    uint8_t postdiv_shift;
    uint8_t postdiv_width;
};

/**
 * Refer to section 5.1.5.4.3 Peripheral clock slice in datasheet.
 */
struct clk_common_slice_data {
    /* Common */
    uint32_t offset;
    /* Mux */
    uint8_t mux_shift;
    uint8_t mux_mask;
    /* Gate */
    uint8_t gate_shift;
    /* Prev Divider */
    uint8_t prevdiv_shift;
    uint8_t prevdiv_width;
    /* Post Divider */
    uint8_t postdiv_shift;
    uint8_t postdiv_width;
};

extern const struct clk_ops clk_gate2_ops;
extern const struct clk_ops clk_frac_pll_ops;
extern const struct clk_ops clk_sscg_pll_ops;
extern const struct clk_ops clk_core_slice_ops;
extern const struct clk_ops clk_bus_slice_ops;
extern const struct clk_ops clk_common_slice_ops;

struct clk **get_clk_list(void);

#define IMX_CLK_SOURCE(_name, _rate)                        \
struct clk _name = {                                        \
    .data = &(struct clk_source_data){                      \
        .rate = (_rate),                                    \
    },                                                      \
    .hw.init = &(struct clk_init_data){                     \
        .name = #_name,                                     \
        .ops = &clk_source_ops,                             \
    }                                                       \
}

/* need to see difference between fixed clk and source clk */
#define IMX_CLK_FIXED(_name, _rate)                         \
IMX_CLK_SOURCE(_name, _rate)

#define IMX_CLK_MUX_FLAGS(_name, _base, _offset, _shift, _width, _parent_data, _num_parents, _init_flags) \
struct clk _name = {                                               \
    .base = (_base),                                               \
    .data = &(struct clk_mux_data) {                               \
        .offset = (_offset),                                       \
        .mask = MASK(_width),                                      \
        .shift = (_shift),                                         \
    },                                                             \
    .hw.init = &(struct clk_init_data) {                           \
        .name = #_name,                                            \
        .ops = &clk_mux_ops,                                       \
        .parent_data = (_parent_data),                             \
        .num_parents = (_num_parents),                             \
        .flags = (_init_flags),                                    \
    },                                                             \
}

#define IMX_CLK_MUX(_name, _base, _offset, _shift, _width, _parent_data, _num_parents)                     \
IMX_CLK_MUX_FLAGS(_name, _base, _offset, _shift, _width,           \
            _parent_data, _num_parents, 0)

#define IMX_CLK_MUX2(_name, _base, _offset, _shift, _width, _parent_data, _num_parents)            \
IMX_CLK_MUX_FLAGS(_name, _base, _offset, _shift, _width,    \
            _parent_data, _num_parents, CLK_OPS_PARENT_ENABLE)

#define IMX_CLK_MUX2_FLAGS(_name, _base, _offset, _shift, _width, _parent_data, _num_parents, _flags)    \
IMX_CLK_MUX_FLAGS(_name, _base, _offset, _shift, _width,          \
            _parent_data, _num_parents, _flags | CLK_OPS_PARENT_ENABLE)

#define IMX_CLK_DIV_FLAGS(_name, _parent_clks, _base, _offset, _shift, _width, _flags)  \
struct clk _name = {                                        \
    .base = (_base),                                        \
    .data = &(struct clk_div_data) {                        \
        .offset = (_offset),                                \
        .shift = (_shift),                                  \
        .width = (_width),                                  \
    },                                                      \
    .hw.init = &(struct clk_init_data) {                    \
        .name = #_name,                                     \
        .ops = &clk_divider_ops,                            \
        .parent_clks = (const struct clk *[]) _parent_clks, \
        .num_parents = 1,                                   \
        .flags = 0,                                         \
    },                                                      \
}

#define IMX_CLK_DIV(_name, _parent_clks, _base, _offset, _shift, _width) \
IMX_CLK_DIV_FLAGS(_name, _parent_clks, _base, _offset, _shift, _width, 0)

#define IMX_CLK_DIV2(_name, _parent_clks, _base, _offset, _shift, _width) \
IMX_CLK_DIV_FLAGS(_name, _parent_clks, _base, _offset, _shift,            \
                  _width, CLK_SET_RATE_PARENT | CLK_OPS_PARENT_ENABLE)

#define IMX_CLK_FRAC_PLL(_name, _parent_clks, _base, _offset)  \
struct clk _name = {                                           \
    .base = (_base),                                           \
    .data = &(struct clk_frac_pll_data) {                      \
        .offset = (_offset),                                   \
    },                                                         \
    .hw.init = &(struct clk_init_data) {                       \
        .name = #_name,                                        \
        .ops = &clk_frac_pll_ops,                              \
        .parent_clks = (const struct clk *[]) _parent_clks,    \
        .num_parents = 1,                                      \
    },                                                         \
}

#define IMX_CLK_GATE1(_name, _parent_clks, _base, _offset, _shift)  \
CLK_GATE(_name, _offset, _shift, 0, _parent_clks, 1, 0)

#define IMX_CLK_GATE(_name, _parent_clks, _base, _offset, _shift)   \
struct clk _name = {                                                \
    .base = (_base),                                                \
    .data = &(struct clk_gate_data) {                               \
        .offset = (_offset),                                        \
        .bit_idx = (_shift),                                        \
    },                                                              \
    .hw.init = &(struct clk_init_data) {                            \
        .name = #_name,                                             \
        .ops = &clk_gate_ops,                                       \
        .parent_clks = (const struct clk *[]) _parent_clks,         \
        .num_parents = 1,                                           \
    },                                                              \
}

#define IMX_CLK_GATE2_FLAGS(_name, _parent_clks, _base, _offset, _shift, _flags) \
struct clk _name = {                                                \
    .base = (_base),                                                \
    .data = &(struct clk_gate_data) {                               \
        .offset = (_offset),                                        \
        .bit_idx = (_shift),                                        \
    },                                                              \
    .hw.init = &(struct clk_init_data) {                            \
        .name = #_name,                                             \
        .ops = &clk_gate2_ops,                                      \
        .parent_clks = (const struct clk *[]) _parent_clks,         \
        .num_parents = 1,                                           \
    },                                                              \
}

#define IMX_CLK_GATE2_SHARED2(_name, _parent_clks, _base, _offset, _shift, _shared_count)                               \
IMX_CLK_GATE2_FLAGS(_name, _parent_clks, _base, _offset, _shift, 0)

#define IMX_CLK_GATE4(_name, _parent_clks, _base, _offset, _shift) \
IMX_CLK_GATE2_FLAGS(_name, _parent_clks, _base, _offset, _shift, 0)

#define IMX_CLK_FIXED_FACTOR(_name, _parent_clks, _mult, _div)      \
CLK_FIXED_FACTOR(_name, _mult, _div, 0, _parent_clks, 1, CLK_SET_RATE_PARENT)

#define IMX_CLK_SSCG_PLL(_name, _parent_data, _num_parents, _parent, _bypass1, _bypass2, _base, _offset, _flags)          \
struct clk _name = {                                                \
    .base = (_base),                                                \
    .data = &(struct clk_sscg_pll_data) {                           \
        .offset = (_offset),                                        \
        .parent = (_parent),                                        \
        .bypass1 = (_bypass1),                                      \
        .bypass2 = (_bypass2),                                      \
    },                                                              \
    .hw.init = &(struct clk_init_data) {                            \
        .name = #_name,                                             \
        .ops = &clk_sscg_pll_ops,                                   \
        .parent_data = (_parent_data),                              \
        .num_parents = 1,                                           \
        .flags = _flags,                                            \
    },                                                              \
}

#define IMX_CLK_COMPOSITE_CORE(_name, _parent_data, _base, _offset) \
struct clk _name = {                                                \
    .base = (_base),                                                \
    .data = &(struct clk_core_slice_data) {                         \
        .offset = (_offset),                                        \
        .mux_shift = PCG_PCS_SHIFT,                                 \
        .mux_mask = PCG_PCS_MASK,                                   \
        .div_shift = PCG_DIV_SHIFT,                                 \
        .div_width = PCG_CORE_DIV_WIDTH,                            \
        .gate_shift = PCG_CGC_SHIFT,                                \
    },                                                              \
    .hw.init = &(struct clk_init_data) {                            \
        .name = #_name,                                             \
        .ops = &clk_core_slice_ops,                                 \
        .parent_data = (_parent_data),                              \
        .num_parents = ARRAY_SIZE(_parent_data),                    \
        .flags = (CLK_DIVIDER_ROUND_CLOSEST |                       \
                  CLK_SET_RATE_NO_REPARENT  |                       \
                  CLK_OPS_PARENT_ENABLE)                            \
    },                                                              \
}

#define IMX_CLK_COMPOSITE_BUS(_name, _parent_data, _base, _offset)  \
struct clk _name = {                                                \
    .base = (_base),                                                \
    .data = &(struct clk_bus_slice_data) {                          \
        .offset = (_offset),                                        \
        .mux_shift = PCG_PCS_SHIFT,                                 \
        .mux_mask = PCG_PCS_MASK,                                   \
        .prevdiv_shift = PCG_PREDIV_SHIFT,                          \
        .prevdiv_width = PCG_PREDIV_WIDTH,                          \
        .postdiv_shift = PCG_DIV_SHIFT,                             \
        .postdiv_width = PCG_DIV_WIDTH,                             \
        .gate_shift = PCG_CGC_SHIFT,                                \
    },                                                              \
    .hw.init = &(struct clk_init_data) {                            \
        .name = #_name,                                             \
        .ops = &clk_bus_slice_ops,                                  \
        .parent_data = (_parent_data),                              \
        .num_parents = ARRAY_SIZE(_parent_data),                    \
        .flags = (CLK_DIVIDER_ROUND_CLOSEST |                       \
                  CLK_SET_RATE_NO_REPARENT  |                       \
                  CLK_OPS_PARENT_ENABLE)                            \
    },                                                              \
}

#define IMX_CLK_COMPOSITE_FLAGS(_name, _parent_data, _base, _offset, _flags) \
struct clk _name = {                                                \
    .base = (_base),                                                \
    .data = &(struct clk_common_slice_data) {                       \
        .offset = (_offset),                                        \
        .mux_shift = PCG_PCS_SHIFT,                                 \
        .mux_mask = PCG_PCS_MASK,                                   \
        .prevdiv_shift = PCG_PREDIV_SHIFT,                          \
        .prevdiv_width = PCG_PREDIV_WIDTH,                          \
        .postdiv_shift = PCG_DIV_SHIFT,                             \
        .postdiv_width = PCG_DIV_WIDTH,                             \
        .gate_shift = PCG_CGC_SHIFT,                                \
    },                                                              \
    .hw.init = &(struct clk_init_data) {                            \
        .name = #_name,                                             \
        .ops = &clk_common_slice_ops,                               \
        .parent_data = (_parent_data),                              \
        .num_parents = ARRAY_SIZE(_parent_data),                    \
        .flags = CLK_DIVIDER_ROUND_CLOSEST  |                       \
                  CLK_SET_RATE_NO_REPARENT  |                       \
                  CLK_OPS_PARENT_ENABLE     |                       \
                  (_flags),                                         \
    },                                                              \
}

#define IMX_CLK_COMPOSITE(_name, _parent_data, _base, _offset)      \
IMX_CLK_COMPOSITE_FLAGS(_name, _parent_data, _base, _offset,        \
                        CLK_OPS_PARENT_ENABLE)

#define IMX_CLK_COMPOSITE_FW_MANAGED(_name, _parent_data, _base, _offset)  \
IMX_CLK_COMPOSITE_FLAGS(_name, _parent_data, _base, _offset,               \
                        (CLK_SET_RATE_NO_REPARENT | CLK_OPS_PARENT_ENABLE  \
                         | CLK_GET_RATE_NOCACHE))

#define IMX_CLK_COMPOSITE_FW_MANAGED_CRITICAL(_name, _parent_data, _base, _offset)                     \
IMX_CLK_COMPOSITE_FLAGS(_name, _parent_data, _base, _offset,               \
                        (CLK_SET_RATE_NO_REPARENT |                        \
                         CLK_OPS_PARENT_ENABLE |                           \
                         CLK_GET_RATE_NOCACHE | CLK_IS_CRITICAL))
