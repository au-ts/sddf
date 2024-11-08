#pragma once

#include <stdint.h>

#define CLK_MESON_MPLL_ROUND_CLOSEST       BIT(0)
#define CLK_MESON_MPLL_SPREAD_SPECTRUM     BIT(1)

#define CLK_MESON_PLL_ROUND_CLOSEST    BIT(0)
#define CLK_MESON_PLL_NOINIT_ENABLED    BIT(1)

/* SPDX-License-Identifier: GPL-2.0-only */
/*
 * Copyright (c) 2015 Endless Mobile, Inc.
 * Author: Carlo Caione <carlo@endlessm.com>
 *
 * Derived from: https://github.com/torvalds/linux/blob/6485cf5ea253d40d507cd71253c9568c5470cd27/drivers/clk/meson/parm.h
 */
/**
 * struct parm - struct defines bits of a clock control field in registers
 *
 * @reg_off:    offset of the register
 * @shift:      shift of the control field
 * @width:      width of the control field
 *
 * Register/value pairs for sequences of writes with an optional delay in
 * microseconds to be applied after each write.
 */
struct parm {
    uint16_t reg_off;
    uint8_t shift;
    uint8_t width;
};

/* SPDX-License-Identifier: GPL-2.0-only */
/*
 * Copyright 2011 Wolfson Microelectronics plc
 *
 * Author: Mark Brown <broonie@opensource.wolfsonmicro.com>
 *
 * Derived from: https://github.com/torvalds/linux/blob/6485cf5ea253d40d507cd71253c9568c5470cd27/include/linux/regmap.h
 */
/**
 * struct reg_sequence - An individual write from a sequence of writes.
 *
 * @reg: Register address.
 * @def: Register value.
 * @delay_us: Delay to be applied after the register write in microseconds
 */
struct reg_sequence {
    unsigned int reg;
    unsigned int def;
    unsigned int delay_us;
};

/* SPDX-License-Identifier: GPL-2.0-only */
/*
 * Copyright (c) 2019 BayLibre, SAS.
 * Author: Jerome Brunet <jbrunet@baylibre.com>
 */
/**
 * struct reg_sequence - An individual write from a sequence of writes.
 *
 * @m: Register address.
 * @n: Register value.
 * @delay_us: Delay to be applied after the register write in microseconds
 *
 * Register/value pairs for sequences of writes with an optional delay in
 * microseconds to be applied after each write.
 */
struct pll_params_table {
    unsigned int m;
    unsigned int n;
};

struct meson_clk_cpu_dyndiv_data {
    struct parm div;
    struct parm dyn;
};

struct meson_clk_pll_data {
    struct parm en;
    struct parm m;
    struct parm n;
    struct parm frac;
    struct parm l;
    struct parm rst;
    struct parm current_en;
    struct parm l_detect;
    const struct reg_sequence *init_regs;
    unsigned int init_count;
    const struct pll_params_table *table;
    /* const struct pll_mult_range *range; */
    uint8_t range_min;
    uint8_t range_max;
    uint8_t flags;
};

struct meson_clk_mpll_data {
    struct parm sdm;
    struct parm sdm_en;
    struct parm n2;
    struct parm ssen;
    struct parm misc;
    const struct reg_sequence *init_regs;
    unsigned int init_count;
    /* spinlock_t *lock; */
    uint8_t flags;
};

struct meson_vid_pll_div_data {
    struct parm val;
    struct parm sel;
};

struct meson_vclk_gate_data {
    struct parm enable;
    struct parm reset;
    uint8_t flags;
};

struct meson_vclk_div_data {
    struct parm div;
    struct parm enable;
    struct parm reset;
    const struct clk_div_table *table;
    uint8_t flags;
};

extern const struct clk_ops meson_clk_pll_ops;
extern const struct clk_ops meson_clk_pll_ro_ops;
extern const struct clk_ops meson_clk_mpll_ops;
extern const struct clk_ops meson_clk_pcie_pll_ops;
extern const struct clk_ops meson_vid_pll_div_ro_ops;
extern const struct clk_ops meson_vclk_gate_ops;
extern const struct clk_ops meson_vclk_div_ops;
extern const struct clk_ops meson_clk_cpu_dyndiv_ops;

#define MESON_CLK81_GATE(_name, _reg, _bit)                  \
struct clk _name = {                                         \
    .data = &(struct clk_gate_data) {                        \
        .offset = (_reg),                                    \
        .bit_idx = (_bit),                                   \
        .flags = 0,                                          \
    },                                                       \
    .hw.init = &(struct clk_init_data) {                     \
        .name = #_name,                                      \
        .ops = &clk_gate_ops,                                \
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
        .ops = &clk_gate_ro_ops,                             \
        .parent_clks = (const struct clk *[]) {              \
            &g12a_clk81,                                     \
        },                                                   \
        .num_parents = 1,                                    \
        .flags = 0,                                          \
    },                                                       \
}

extern const struct clk g12a_xtal;
struct clk **get_clk_list(void);
