// SPDX-License-Identifier: (GPL-2.0 OR BSD-3-Clause)
/*
 * Operations for MPLL clocks are derived from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/meson/clk-mpll.c
 *
 * Copyright (c) 2016 AmLogic, Inc.
 * Author: Michael Turquette <mturquette@baylibre.com>
 */

// SPDX-License-Identifier: GPL-2.0
/*
 * Operations for PLL clocks are derived from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/meson/clk-pll.c
 *
 * Copyright (c) 2015 Endless Mobile, Inc.
 * Author: Carlo Caione <carlo@endlessm.com>
 *
 * Copyright (c) 2018 Baylibre, SAS.
 * Author: Jerome Brunet <jbrunet@baylibre.com>
 */

// SPDX-License-Identifier: GPL-2.0
/*
 * Operations for gate clocks are derived from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/meson/clk-regmap.c
 *
 * Copyright (c) 2018 BayLibre, SAS.
 * Author: Jerome Brunet <jbrunet@baylibre.com>
 */

// SPDX-License-Identifier: GPL-2.0
/*
 * Operations for fixed factor clocks are derived from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/clk-fixed-factor.c
 *
 * Copyright (C) 2011 Sascha Hauer, Pengutronix <s.hauer@pengutronix.de>
 */

// SPDX-License-Identifier: GPL-2.0
/*
 * Operations for divider clocks are derived from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/clk-divider.c
 *
 * Copyright (C) 2011 Sascha Hauer, Pengutronix <s.hauer@pengutronix.de>
 * Copyright (C) 2011 Richard Zhao, Linaro <richard.zhao@linaro.org>
 * Copyright (C) 2011-2012 Mike Turquette, Linaro Ltd <mturquette@linaro.org>
 *
 * Adjustable divider clock implementation
 */

// SPDX-License-Identifier: GPL-2.0
/*
 * Operations for multiplexer clocks are derived from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/clk-mux.c
 *
 * Copyright (C) 2011 Sascha Hauer, Pengutronix <s.hauer@pengutronix.de>
 * Copyright (C) 2011 Richard Zhao, Linaro <richard.zhao@linaro.org>
 * Copyright (C) 2011-2012 Mike Turquette, Linaro Ltd <mturquette@linaro.org>
 *
 * Simple multiplexer clock implementation
 */

// SPDX-License-Identifier: GPL-2.0
/*
 * Operations for meson_vid_pll_div are derived from:
 *   https://github.com/torvalds/linux/blob/7ec462100ef9142344ddbf86f2c3008b97acddbe/drivers/clk/meson/vid-pll-div.c
 *   https://github.com/torvalds/linux/blob/7ec462100ef9142344ddbf86f2c3008b97acddbe/drivers/clk/meson/vclk.c
 *
 * Copyright (c) 2018 BayLibre, SAS.
 * Author: Neil Armstrong <narmstrong@baylibre.com>
 */

#include <clk.h>
#include <utils.h>
#include <clk-operations.h>
#include <sddf/timer/client.h>
#include <sddf/util/printf.h>

int reg_write(uint64_t base, uint32_t offset, uint32_t val)
{
    volatile uint32_t *clk_reg = ((void *)base + offset);
    *clk_reg = val;

    return 0;
}

int regmap_update_bits(uint64_t base, uint32_t offset, uint8_t shift, uint8_t width, uint32_t val)
{
    volatile uint32_t *clk_reg = ((void *)base + offset);
    uint32_t reg_val = *clk_reg;

    reg_val &= ~(MASK(width) << shift);
    reg_val |= ((MASK(width) & val) << shift);

    *clk_reg = reg_val;

    /* TODO: Check if the register has been updated correctly */

    return 0;
}

int regmap_read_bits(uint64_t base, uint32_t offset, uint8_t shift, uint8_t width)
{
    volatile uint32_t *clk_reg = ((void *)base + offset);
    uint32_t reg_val = *clk_reg;

    reg_val >>= shift;
    reg_val &= MASK(width);

    return reg_val;
}

int regmap_mux_update_bits(uint64_t base, uint32_t offset, uint8_t shift, uint32_t mask, uint32_t val)
{
    volatile uint32_t *clk_reg = ((void *)base + offset);
    uint32_t reg_val = *clk_reg;

    reg_val &= ~(mask << shift);
    reg_val |= ((mask & val) << shift);

    *clk_reg = reg_val;

    /* TODO: Check if the register has been updated correctly */

    return 0;
}

int regmap_mux_read_bits(uint64_t base, uint32_t offset, uint8_t shift, uint32_t mask)
{
    volatile uint32_t *clk_reg = ((void *)base + offset);
    uint32_t reg_val = *clk_reg;

    reg_val >>= shift;
    reg_val &= mask;

    return reg_val;
}

static int clk_gate_enable(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    return regmap_update_bits(clk->base, data->offset, data->bit_idx, 1, 1);
}

static int clk_gate_disable(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    regmap_update_bits(clk->base, data->offset, data->bit_idx, 1, 0);
    return 0;
}

static int clk_gate_is_enabled(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    /* TODO: to be checked */
    /* if (gate->flags & CLK_GATE_SET_TO_DISABLE) */
    /*     val ^= BIT(gate->bit_idx); */

    /* val &= BIT(gate->bit_idx); */
    /* return val ? 1 : 0; */

    return regmap_read_bits(clk->base, data->offset, data->bit_idx, 1);
}

const struct clk_ops clk_gate_ops = {
    .enable = clk_gate_enable,
    .disable = clk_gate_disable,
    .is_enabled = clk_gate_is_enabled,
};

const struct clk_ops clk_gate_ro_ops = {
    .is_enabled = clk_gate_is_enabled,
};

static unsigned long clk_div_recalc_rate(const struct clk *clk,
                                unsigned long prate)
{

    struct clk_div_data *data = (struct clk_div_data *)(clk->data);
    uint32_t div = regmap_read_bits(clk->base, data->offset, data->shift, data->width);

    /* TODO: Need to verify the following cases */
    if (data->flags & CLK_DIVIDER_ONE_BASED) {
        ;
    } else if (data->flags & CLK_DIVIDER_POWER_OF_TWO) {
        div = 1 << div;
    } else if (data->flags & CLK_DIVIDER_MAX_AT_ZERO) {
        div = div ? div: MASK(data->width) + 1;
    } else {
        div += 1;
    }

    return DIV_ROUND_UP_ULL((uint64_t)prate, div);
}

static int clk_div_set_rate(const struct clk *clk, uint32_t rate, uint32_t parent_rate)
{
    struct clk_div_data *data = (struct clk_div_data *)(clk->data);
    uint32_t div = DIV_ROUND_UP(parent_rate, rate);

    if (data->flags & CLK_DIVIDER_ONE_BASED) {
        /* TODO: to be implemented */
        ;
    } else if (data->flags & CLK_DIVIDER_POWER_OF_TWO) {
        /* div = __ffs(div); */
    } else if (data->flags & CLK_DIVIDER_MAX_AT_ZERO) {
        div = (div == MASK(data->width) + 1) ? 0 : div;
    } else {
        div -= 1;
    }
    return regmap_update_bits(clk->base, data->offset, data->shift, data->width, div);
}

/* static int clk_div_determine_rate(struct clk_hw *hw, */
/*                      struct clk_rate_request *req) */
/* { */
/*     struct clk_div_data *data = (struct clk_div_data *)(hw->clk->data); */
/*     /\* struct clk_regmap *clk = to_clk_regmap(hw); *\/ */
/*     /\* struct clk_div_data *div = clk_get_regmap_div_data(clk); *\/ */
/*     uint32_t val; */

/*     /\* if read only, just return current value *\/ */
/*     if (data->flags & CLK_DIVIDER_READ_ONLY) { */
/*         val = regmap_read_bits(data->offset, data->shift, data->width); */

/*         /\* return divider_ro_determine_rate(hw, req, div->table, *\/ */
/*                          /\* div->width, div->flags, val); *\/ */
/*     } */

/*     /\* return divider_determine_rate(hw, req, div->table, div->width, *\/ */
/*                       /\* div->flags); *\/ */
/*     return 0; */
/* } */

const struct clk_ops clk_divider_ops = {
    .enable = NULL,
    .recalc_rate = clk_div_recalc_rate,
    /* .determine_rate = clk_div_determine_rate, */
    .set_rate = clk_div_set_rate,
};

const struct clk_ops clk_divider_ro_ops = {
    .recalc_rate = clk_div_recalc_rate,
    /* .determine_rate = clk_div_determine_rate, */
};

static uint8_t clk_mux_get_parent(const struct clk *clk)
{
    struct clk_mux_data *data = (struct clk_mux_data *)(clk->data);
    uint32_t num_parents = clk->hw.init->num_parents;
    uint32_t val = regmap_mux_read_bits(clk->base, data->offset, data->shift, data->mask);

    if (data->table) {
        int i;
        for (i = 0; i < num_parents; i++) {
            if (data->table[i] == val)
                return i;
        }
        return -1;
        /* return -EINVAL; */
    }

    /* if (val && (flags & CLK_MUX_INDEX_BIT)) */
    /*     val = ffs(val) - 1; */

    /* if (val && (flags & CLK_MUX_INDEX_ONE)) */
    /*     val--; */

    if (val >= num_parents)
        /* return -EINVAL; */
        return -1;

    /* return val; */
    return 0;
}

static int clk_mux_set_parent(struct clk *clk, uint8_t index)
{
    struct clk_mux_data *data = (struct clk_mux_data *)(clk->data);

    if (data->table) {
        unsigned int val = data->table[index];
        regmap_mux_update_bits(clk->base, data->offset, data->shift, data->mask, val);
    }
    /* TODO: handle cases without table given */

    return 0;
}

const struct clk_ops clk_mux_ops = {
    .get_parent = clk_mux_get_parent,
    .set_parent = clk_mux_set_parent,
    /* .determine_rate = clk_mux_determine_rate, */
};

const struct clk_ops clk_mux_ro_ops = {
    .get_parent = clk_mux_get_parent,
};

static unsigned long clk_factor_recalc_rate(const struct clk *clk,
        unsigned long parent_rate)
{
    struct clk_fixed_factor_data *data = (struct clk_fixed_factor_data *)(clk->data);
    unsigned long long int rate;

    rate = (unsigned long long int)parent_rate * data->mult;
    do_div(rate, data->div);
    return (unsigned long)rate;
}

const struct clk_ops clk_fixed_factor_ops = {
    /* .round_rate = clk_factor_round_rate, */
    /* .set_rate = clk_factor_set_rate, */
    .recalc_rate = clk_factor_recalc_rate,
    /* .recalc_accuracy = clk_factor_recalc_accuracy, */
};

static int clk_source_set_rate(const struct clk *clk, uint32_t rate, uint32_t parent_rate)
{
    struct clk_source_data *data = (struct clk_source_data *)(clk->data);
    data->rate = rate;

    return 0;
}

static unsigned long clk_source_get_rate(const struct clk *clk,
                                unsigned long prate)
{
    struct clk_source_data *data = (struct clk_source_data *)(clk->data);

    return data->rate;
}

const struct clk_ops clk_source_ops = {
    .recalc_rate = clk_source_get_rate,
    .set_rate = clk_source_set_rate,
};
