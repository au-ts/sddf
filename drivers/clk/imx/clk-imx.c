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

#include <clk_utils.h>
#include <clk-operations.h>
#include <clk-imx.h>

#define PLL_FRAC_DENOM 0x1000000

static int clk_gate2_enable(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    return regmap_update_bits(clk->base, data->offset, data->bit_idx, MASK(2), 0x3);
}

static int clk_gate2_disable(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    return regmap_update_bits(clk->base, data->offset, data->bit_idx, MASK(2), 0);
}

static int clk_gate2_is_enabled(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    if (regmap_read_bits(clk->base, data->offset, data->bit_idx, MASK(2)) == 0x3)
        return 1;

    return 0;
}

const struct clk_ops clk_gate2_ops = {
    .enable = clk_gate2_enable,
    .disable = clk_gate2_disable,
    /* .disable_unused = clk_gate2_disable_unused, */
    .is_enabled = clk_gate2_is_enabled,
};

static uint64_t clk_pll_recalc_rate(const struct clk *clk, uint64_t prate)
{
    /* TODO: This function is derived from Linux codebase, but seems wrong
     * according to the datasheet as PLL_REFCLK_DIV_VAL[5:10] is never used. */
    struct clk_frac_pll_data *data = (struct clk_frac_pll_data *)(clk->data);
    uint64_t temp_rate = prate;
    uint64_t rate;

    /* Output Divider value is (n + 1) * 2 */
    uint32_t output_div_val = regmap_read_bits(clk->base, data->offset, 0, MASK(5));
    output_div_val = (output_div_val + 1) * 2;

    /* Valid Frac Divider value is 1 to 2^24 */
    uint32_t frac_div_val = regmap_read_bits(clk->base, data->offset + 0x4, 7, MASK(24));

    /* Valid Int Divider value is 1 to 32 */
    uint32_t int_div_val = regmap_read_bits(clk->base, data->offset + 0x4, 0, MASK(7));

    temp_rate *= prate;
    temp_rate *= frac_div_val;
    do_div(temp_rate, PLL_FRAC_DENOM);
    do_div(temp_rate, output_div_val);

    /* Frac Divider value is (n) */
    rate = prate * 8 * (int_div_val + 1);
    do_div(rate, output_div_val);
    rate += temp_rate;

    return rate;
}

const struct clk_ops clk_frac_pll_ops = {
    /* .prepare     = clk_pll_prepare, */
    /* .unprepare   = clk_pll_unprepare, */
    /* .is_prepared = clk_pll_is_prepared, */
    .recalc_rate = clk_pll_recalc_rate,
    /* .round_rate  = clk_pll_round_rate, */
    /* .set_rate    = clk_pll_set_rate, */
};

static uint64_t clk_sscg_pll_recalc_rate(const struct clk *clk, uint64_t prate)
{
    struct clk_sscg_pll_data *data = (struct clk_sscg_pll_data *)(clk->data);
    uint64_t temp_rate = prate;

    uint32_t divr1 = regmap_read_bits(clk->base, data->offset + 0x8, 25, MASK(3));
    uint32_t divr2 = regmap_read_bits(clk->base, data->offset + 0x8, 19, MASK(6));
    uint32_t divf1 = regmap_read_bits(clk->base, data->offset + 0x8, 13, MASK(6));
    uint32_t divf2 = regmap_read_bits(clk->base, data->offset + 0x8, 7, MASK(6));
    uint32_t divq = regmap_read_bits(clk->base, data->offset + 0x8, 1, MASK(6));

    if (regmap_read_bits(clk->base, data->offset, 4, MASK(1))) {
        temp_rate = prate;
    } else if (regmap_read_bits(clk->base, data->offset, 5, MASK(1))) {
        temp_rate *= divf2;
        do_div(temp_rate, (divr2 + 1) * (divq + 1));
    } else {
        temp_rate *= 2;
        temp_rate *= (divf1 + 1) * (divf2 + 1);
        do_div(temp_rate, (divr1 + 1) * (divr2 + 1) * (divq + 1));
    }

    return 0;
}

static uint8_t clk_sscg_pll_get_parent(const struct clk *clk)
{
    struct clk_sscg_pll_data *data = (struct clk_sscg_pll_data *)(clk->data);
    uint8_t ret = 0;

    if (regmap_read_bits(clk->base, data->offset, 4, MASK(1))) {
        ret = data->bypass2;
    } else if (regmap_read_bits(clk->base, data->offset, 5, MASK(1))) {
        ret = data->bypass1;
    }

    return ret;
}

static int clk_sscg_pll_set_parent(struct clk *clk, uint8_t index)
{
    // struct clk_sscg_pll_data *data = (struct clk_sscg_pll_data *)(clk->data);

    /* TODO: This operation is based on `setup.bypass` instead of index
     * passed from callee, need to be decided by clock manager */

    return 0;
}

const struct clk_ops clk_sscg_pll_ops = {
    /* .prepare = clk_sscg_pll_prepare, */
    /* .unprepare = clk_sscg_pll_unprepare, */
    /* .is_prepared = clk_sscg_pll_is_prepared, */
    .recalc_rate = clk_sscg_pll_recalc_rate,
    /* .set_rate = clk_sscg_pll_set_rate, */
    .set_parent = clk_sscg_pll_set_parent,
    .get_parent = clk_sscg_pll_get_parent,
    /* .determine_rate = clk_sscg_pll_determine_rate, */
};

static uint64_t imx8m_clk_core_slice_recalc_rate(const struct clk *clk, uint64_t prate)
{
    struct clk_core_slice_data *data = (struct clk_core_slice_data *)(clk->data);

    uint32_t div_val = regmap_read_bits(clk->base, data->offset, data->div_shift, MASK(data->div_width));
    /* Divider value is n+1 */
    return DIV_ROUND_UP_ULL((uint64_t)prate, div_val + 1);
}

static uint8_t imx8m_clk_core_slice_get_parent(const struct clk *clk)
{
    struct clk_core_slice_data *data = (struct clk_core_slice_data *)(clk->data);

    uint32_t num_parents = clk->hw.init->num_parents;
    uint32_t val = regmap_read_bits(clk->base, data->offset, data->mux_shift, data->mux_mask);

    if (val >= num_parents)
        return -1;

    return val;
}

static int imx8m_clk_core_slice_set_parent(struct clk *clk, uint8_t index)
{
    struct clk_core_slice_data *data = (struct clk_core_slice_data *)(clk->data);

    /*
     * write twice to make sure non-target interface
     * SEL_A/B point the same clk input.
     */
    regmap_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);
    regmap_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);

    return 0;
}

const struct clk_ops clk_core_slice_ops = {
    .recalc_rate = imx8m_clk_core_slice_recalc_rate,
    /* .round_rate = imx8m_clk_core_slice_round_rate, */
    /* .set_rate = imx8m_clk_core_slice_set_rate, */
    /* .determine_rate = imx8m_clk_core_slice_determine_rate, */
    .get_parent = imx8m_clk_core_slice_get_parent,
    .set_parent = imx8m_clk_core_slice_set_parent,
};

static uint64_t imx8m_clk_common_slice_recalc_rate(const struct clk *clk, uint64_t prate)
{
    struct clk_common_slice_data *data = (struct clk_common_slice_data *)(clk->data);

    uint32_t prediv_val = regmap_read_bits(clk->base, data->offset, data->prevdiv_shift, MASK(data->prevdiv_width));
    /* Divider value is n+1 */
    uint64_t prediv_rate = DIV_ROUND_UP_ULL((uint64_t)prate, prediv_val + 1);

    uint32_t postdiv_val = regmap_read_bits(clk->base, data->offset, data->postdiv_shift, MASK(data->postdiv_width));
    /* Divider value is n+1 */
    return DIV_ROUND_UP_ULL((uint64_t)prediv_rate, postdiv_val + 1);
}

static uint8_t imx8m_clk_common_slice_get_parent(const struct clk *clk)
{
    struct clk_common_slice_data *data = (struct clk_common_slice_data *)(clk->data);

    uint32_t num_parents = clk->hw.init->num_parents;
    uint32_t val = regmap_read_bits(clk->base, data->offset, data->mux_shift, data->mux_mask);

    if (val >= num_parents)
        return -1;

    return val;
}

static int imx8m_clk_common_slice_set_parent(struct clk *clk, uint8_t index)
{
    struct clk_common_slice_data *data = (struct clk_common_slice_data *)(clk->data);

    /*
     * write twice to make sure non-target interface
     * SEL_A/B point the same clk input.
     */
    regmap_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);
    regmap_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);

    return 0;
}

const struct clk_ops clk_common_slice_ops = {
    .recalc_rate = imx8m_clk_common_slice_recalc_rate,
    /* .round_rate = imx8m_clk_common_slice_round_rate, */
    /* .set_rate = imx8m_clk_common_slice_set_rate, */
    /* .determine_rate = imx8m_clk_common_slice_determine_rate, */
    .get_parent = imx8m_clk_common_slice_get_parent,
    .set_parent = imx8m_clk_common_slice_set_parent,
};

static uint64_t imx8m_clk_bus_slice_recalc_rate(const struct clk *clk, uint64_t prate)
{
    struct clk_bus_slice_data *data = (struct clk_bus_slice_data *)(clk->data);

    uint32_t prediv_val = regmap_read_bits(clk->base, data->offset, data->prevdiv_shift, MASK(data->prevdiv_width));
    /* Divider value is n+1 */
    uint64_t prediv_rate = DIV_ROUND_UP_ULL((uint64_t)prate, prediv_val + 1);

    uint32_t postdiv_val = regmap_read_bits(clk->base, data->offset, data->postdiv_shift, MASK(data->postdiv_width));
    /* Divider value is n+1 */
    return DIV_ROUND_UP_ULL((uint64_t)prediv_rate, postdiv_val + 1);
}

static uint8_t imx8m_clk_bus_slice_get_parent(const struct clk *clk)
{
    struct clk_bus_slice_data *data = (struct clk_bus_slice_data *)(clk->data);

    uint32_t num_parents = clk->hw.init->num_parents;
    uint32_t val = regmap_read_bits(clk->base, data->offset, data->mux_shift, data->mux_mask);

    if (val >= num_parents)
        return -1;

    return val;
}

static int imx8m_clk_bus_slice_set_parent(struct clk *clk, uint8_t index)
{
    struct clk_bus_slice_data *data = (struct clk_bus_slice_data *)(clk->data);

    /*
     * write twice to make sure non-target interface
     * SEL_A/B point the same clk input.
     */
    regmap_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);
    regmap_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);

    return 0;
}

const struct clk_ops clk_bus_slice_ops = {
    .recalc_rate = imx8m_clk_bus_slice_recalc_rate,
    /* .round_rate = imx8m_clk_composite_divider_round_rate, */
    /* .set_rate = imx8m_clk_composite_divider_set_rate, */
    /* .determine_rate = imx8m_divider_determine_rate, */
    .get_parent = imx8m_clk_bus_slice_get_parent,
    .set_parent = imx8m_clk_bus_slice_set_parent,
};
