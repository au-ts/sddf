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

#include <clk-operations.h>
#include <sddf/timer/client.h>
#include <sddf/util/printf.h>

#define TIMER_CH 1

uintptr_t clk_base;

void init_clk_base(uintptr_t base_addr)
{
    clk_base = base_addr;
}

static inline int reg_write(uint32_t offset, uint32_t val)
{
    volatile uint32_t *clk_reg = ((void *)clk_base + offset);
    *clk_reg = val;

    return 0;
}

static inline int regmap_update_bits(uint32_t offset, uint8_t shift, uint8_t width, uint32_t val)
{
    volatile uint32_t *clk_reg = ((void *)clk_base + offset);
    uint32_t reg_val = *clk_reg;

    reg_val &= ~(MASK(width) << shift);
    reg_val |= ((MASK(width) & val) << shift);

    *clk_reg = reg_val;

    /* TODO: Check if the register has been updated correctly */

    return 0;
}

static inline int regmap_read_bits(uint32_t offset, uint8_t shift, uint8_t width)
{
    volatile uint32_t *clk_reg = ((void *)clk_base + offset);
    uint32_t reg_val = *clk_reg;

    reg_val >>= shift;
    reg_val &= MASK(width);

    return reg_val;
}

static inline int regmap_mux_update_bits(uint32_t offset, uint8_t shift, uint32_t mask, uint32_t val)
{
    volatile uint32_t *clk_reg = ((void *)clk_base + offset);
    uint32_t reg_val = *clk_reg;

    reg_val &= ~(mask << shift);
    reg_val |= ((mask & val) << shift);

    *clk_reg = reg_val;

    /* TODO: Check if the register has been updated correctly */

    return 0;
}

static inline int regmap_mux_read_bits(uint32_t offset, uint8_t shift, uint32_t mask)
{
    volatile uint32_t *clk_reg = ((void *)clk_base + offset);
    uint32_t reg_val = *clk_reg;

    reg_val >>= shift;
    reg_val &= mask;

    return reg_val;
}

static inline uint32_t meson_parm_read(struct parm parm)
{
    return regmap_read_bits(parm.reg_off, parm.shift, parm.width);
}

/* TODO: Replace this doggy dealy() with a standard interface */
void delay_us(uint32_t us)
{
    uint64_t start_time = sddf_timer_time_now(TIMER_CH);
    uint64_t now_time = start_time;
    while (now_time - start_time < us) {
        now_time = sddf_timer_time_now(TIMER_CH);
    }
}

int regmap_multi_reg_write(const struct reg_sequence *regs, int num_regs)
{
    int i;
    for (i = 0; i < num_regs; i++) {
        reg_write(regs[i].reg, regs[i].def);
        /* TODO: delay is needed */
        if (regs[i].delay_us) {
            delay_us(regs[i].delay_us);
        }
    }
    return 0;
}

static int clk_regmap_gate_enable(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    return regmap_update_bits(data->offset, data->bit_idx, 1, 1);
}

static int clk_regmap_gate_disable(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    regmap_update_bits(data->offset, data->bit_idx, 1, 0);
    return 0;
}

static int clk_regmap_gate_is_enabled(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    /* TODO: to be checked */
    /* if (gate->flags & CLK_GATE_SET_TO_DISABLE) */
    /*     val ^= BIT(gate->bit_idx); */

    /* val &= BIT(gate->bit_idx); */
    /* return val ? 1 : 0; */

    return regmap_read_bits(data->offset, data->bit_idx, 1);
}

const struct clk_ops clk_regmap_gate_ops = {
    .enable = clk_regmap_gate_enable,
    .disable = clk_regmap_gate_disable,
    .is_enabled = clk_regmap_gate_is_enabled,
};

const struct clk_ops clk_regmap_gate_ro_ops = {
    .is_enabled = clk_regmap_gate_is_enabled,
};

static unsigned long clk_regmap_div_recalc_rate(const struct clk *clk,
                                unsigned long prate)
{

    struct clk_div_data *data = (struct clk_div_data *)(clk->data);
    uint32_t div = regmap_read_bits(data->offset, data->shift, data->width);

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

static int clk_regmap_div_set_rate(const struct clk *clk, uint32_t rate, uint32_t parent_rate)
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
    return regmap_update_bits(data->offset, data->shift, data->width, div);
}

/* static int clk_regmap_div_determine_rate(struct clk_hw *hw, */
/*                      struct clk_rate_request *req) */
/* { */
/*     struct clk_div_data *data = (struct clk_div_data *)(hw->clk->data); */
/*     /\* struct clk_regmap *clk = to_clk_regmap(hw); *\/ */
/*     /\* struct clk_regmap_div_data *div = clk_get_regmap_div_data(clk); *\/ */
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

const struct clk_ops clk_regmap_divider_ops = {
    .enable = NULL,
    .recalc_rate = clk_regmap_div_recalc_rate,
    /* .determine_rate = clk_regmap_div_determine_rate, */
    .set_rate = clk_regmap_div_set_rate,
};

const struct clk_ops clk_regmap_divider_ro_ops = {
    .recalc_rate = clk_regmap_div_recalc_rate,
    /* .determine_rate = clk_regmap_div_determine_rate, */
};

static uint8_t clk_regmap_mux_get_parent(const struct clk *clk)
{
    struct clk_mux_data *data = (struct clk_mux_data *)(clk->data);
    uint32_t num_parents = clk->hw.init->num_parents;
    uint32_t val = regmap_mux_read_bits(data->offset, data->shift, data->mask);

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

static int clk_regmap_mux_set_parent(struct clk *clk, uint8_t index)
{
    struct clk_mux_data *data = (struct clk_mux_data *)(clk->data);

    if (data->table) {
        unsigned int val = data->table[index];
        regmap_mux_update_bits(data->offset, data->shift, data->mask, val);
    }

    return 0;
}

const struct clk_ops clk_regmap_mux_ops = {
    .get_parent = clk_regmap_mux_get_parent,
    .set_parent = clk_regmap_mux_set_parent,
    /* .determine_rate = clk_regmap_mux_determine_rate, */
};

const struct clk_ops clk_regmap_mux_ro_ops = {
    .get_parent = clk_regmap_mux_get_parent,
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

static void meson_clk_pll_init(struct clk *clk)
{
    struct meson_clk_pll_data *data = (struct meson_clk_pll_data *)(clk->data);
    if ((data->flags & CLK_MESON_PLL_NOINIT_ENABLED) && clk->hw.init->ops->is_enabled(clk))
        return ;

    if (data->init_count) {
        /* Set the reset bit */
        regmap_update_bits(data->rst.reg_off, data->rst.shift, data->rst.width, 1);

        regmap_multi_reg_write(data->init_regs, data->init_count);

        /* Clear the reset bit */
        regmap_update_bits(data->rst.reg_off, data->rst.shift, data->rst.width, 0);
    }
}

static unsigned long meson_clk_pll_recalc_rate(const struct clk *clk,
                        unsigned long parent_rate)
{
    struct meson_clk_pll_data *data = (struct meson_clk_pll_data *)(clk->data);
    uint32_t n, m, frac;

    n = regmap_read_bits(data->n.reg_off, data->n.shift, data->n.width);
    if (n == 0)
        return 0;

    m = regmap_read_bits(data->m.reg_off, data->m.shift, data->m.width);

    frac = data->frac.width ?
            regmap_read_bits(data->frac.reg_off, data->frac.shift, data->frac.width) :
            0;

    uint64_t rate = (uint64_t)parent_rate * m;

    if (frac) {
        uint64_t frac_rate = (uint64_t)parent_rate * frac;
        rate += DIV_ROUND_UP_ULL(frac_rate, (1 << data->frac.width));
    }

    return DIV_ROUND_UP_ULL(rate, n);
}

static int meson_clk_pll_is_enabled(struct clk *clk)
{
    struct meson_clk_pll_data *data = (struct meson_clk_pll_data *)(clk->data);

    if (data->rst.width && meson_parm_read(data->rst)) {
        return 0;
    }

    if (!meson_parm_read(data->en) || !meson_parm_read(data->l)) {
        return 0;
    }

    return 1;
}

static int meson_clk_pll_enable(struct clk *clk)
{
    struct meson_clk_pll_data *data = (struct meson_clk_pll_data *)(clk->data);

    if (meson_clk_pll_is_enabled(clk))
        return 0;

    regmap_update_bits(data->rst.reg_off, data->rst.shift, data->rst.width, 1);
    regmap_update_bits(data->en.reg_off, data->en.shift, data->en.width, 1);
    regmap_update_bits(data->rst.reg_off, data->rst.shift, data->rst.width, 1);

    regmap_update_bits(data->current_en.reg_off, data->current_en.shift, data->current_en.width, 1);
    return 0;
}

static int meson_clk_pll_disable(struct clk *clk)
{
    struct meson_clk_pll_data *data = (struct meson_clk_pll_data *)(clk->data);

    regmap_update_bits(data->rst.reg_off, data->rst.shift, data->rst.width, 1);
    regmap_update_bits(data->en.reg_off, data->en.shift, data->en.width, 0);
    return 0;
}

const struct clk_ops meson_clk_pll_ops = {
    .init           = meson_clk_pll_init,
    .recalc_rate    = meson_clk_pll_recalc_rate,
    /* .determine_rate = meson_clk_pll_determine_rate, */
    /* .set_rate       = meson_clk_pll_set_rate, */
    .is_enabled     = meson_clk_pll_is_enabled,
    .enable         = meson_clk_pll_enable,
    .disable        = meson_clk_pll_disable
};

const struct clk_ops meson_clk_pll_ro_ops = {
    .recalc_rate = meson_clk_pll_recalc_rate,
    .is_enabled    = meson_clk_pll_is_enabled,
};

#define SDM_DEN 16384
#define N2_MIN 4
#define N2_MAX 511

static unsigned long mpll_recalc_rate(const struct clk *clk,
                                unsigned long prate)
{
    struct meson_clk_mpll_data *data = (struct meson_clk_mpll_data *)(clk->data);
    uint32_t sdm, n2;

    sdm = regmap_read_bits(data->sdm.reg_off, data->sdm.shift, data->sdm.width);
    n2 = regmap_read_bits(data->n2.reg_off, data->n2.shift, data->n2.width);

    uint32_t divisor = (SDM_DEN * n2) + sdm;
    if (n2 < N2_MIN)
        return -1;

    return DIV_ROUND_UP_ULL((uint64_t)prate * SDM_DEN, divisor);
}

static int mpll_set_rate(const struct clk *clk,
             uint32_t rate,
             uint32_t parent_rate)
{
    struct meson_clk_mpll_data *data = (struct meson_clk_mpll_data *)(clk->data);
    uint64_t div = parent_rate;
    uint64_t frac = do_div(div, rate);
    uint32_t sdm, n2;

    frac *= SDM_DEN;

    if (data->flags & CLK_MESON_MPLL_ROUND_CLOSEST)
        sdm = DIV_ROUND_CLOSEST_ULL(frac, rate);
    else
        sdm = DIV_ROUND_UP_ULL(frac, rate);

    if (sdm == SDM_DEN) {
        sdm = 0;
        div += 1;
    }

    if (div < N2_MIN) {
        n2 = N2_MIN;
        sdm = 0;
    } else if (div > N2_MAX) {
        n2 = N2_MAX;
        sdm = SDM_DEN - 1;
    } else {
        n2 = div;
    }

    regmap_update_bits(data->sdm.reg_off, data->sdm.shift, data->sdm.width, sdm);
    regmap_update_bits(data->n2.reg_off, data->n2.shift, data->n2.width, n2);

    /* volatile uint32_t *clk_reg = ((void *)clk_base + data->sdm.reg_off); */

    return 0;
}

static void mpll_init(struct clk *clk)
{
    struct meson_clk_mpll_data *data = (struct meson_clk_mpll_data *)(clk->data);
    if (data->init_count) {
        regmap_multi_reg_write(data->init_regs, data->init_count);
    }

    /* Enable the fractional part */
    regmap_update_bits(data->sdm_en.reg_off, data->sdm_en.shift, data->sdm_en.width, 1);

    /* Set spread spectrum if possible */
    unsigned int ss = data->flags & CLK_MESON_MPLL_SPREAD_SPECTRUM ? 1 : 0;
    regmap_update_bits(data->ssen.reg_off, data->ssen.shift, data->ssen.width, ss);
}


const struct clk_ops meson_clk_mpll_ops = {
    .recalc_rate = mpll_recalc_rate,
    /* .determine_rate = mpll_determine_rate, */
    .set_rate = mpll_set_rate,
    .init = mpll_init,
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

const struct clk_ops meson_clk_source_ops = {
    .recalc_rate = clk_source_get_rate,
    .set_rate = clk_source_set_rate,
};

const struct clk_ops meson_clk_pcie_pll_ops = {
    .init           = meson_clk_pll_init,
    /* .recalc_rate    = meson_clk_pll_recalc_rate, */
    /* .determine_rate    = meson_clk_pll_determine_rate, */
    /* .is_enabled    = meson_clk_pll_is_enabled, */
    /* .enable        = meson_clk_pcie_pll_enable, */
    /* .disable    = meson_clk_pll_disable */
};

struct vid_pll_div {
    unsigned int shift_val;
    unsigned int shift_sel;
    unsigned int divider;
    unsigned int multiplier;
};

#define VID_PLL_DIV(_val, _sel, _ft, _fb)       \
    {                                           \
        .shift_val = (_val),                    \
        .shift_sel = (_sel),                    \
        .divider = (_ft),                       \
        .multiplier = (_fb),                    \
    }

static const struct vid_pll_div vid_pll_div_table[] = {
    VID_PLL_DIV(0x0aaa, 0, 2, 1),    /* 2/1  => /2 */
    VID_PLL_DIV(0x5294, 2, 5, 2),    /* 5/2  => /2.5 */
    VID_PLL_DIV(0x0db6, 0, 3, 1),    /* 3/1  => /3 */
    VID_PLL_DIV(0x36cc, 1, 7, 2),    /* 7/2  => /3.5 */
    VID_PLL_DIV(0x6666, 2, 15, 4),   /* 15/4 => /3.75 */
    VID_PLL_DIV(0x0ccc, 0, 4, 1),    /* 4/1  => /4 */
    VID_PLL_DIV(0x739c, 2, 5, 1),    /* 5/1  => /5 */
    VID_PLL_DIV(0x0e38, 0, 6, 1),    /* 6/1  => /6 */
    VID_PLL_DIV(0x0000, 3, 25, 4),   /* 25/4 => /6.25 */
    VID_PLL_DIV(0x3c78, 1, 7, 1),    /* 7/1  => /7 */
    VID_PLL_DIV(0x78f0, 2, 15, 2),   /* 15/2 => /7.5 */
    VID_PLL_DIV(0x0fc0, 0, 12, 1),   /* 12/1 => /12 */
    VID_PLL_DIV(0x3f80, 1, 14, 1),   /* 14/1 => /14 */
    VID_PLL_DIV(0x7f80, 2, 15, 1),   /* 15/1 => /15 */
};

static unsigned long meson_vid_pll_div_recalc_rate(const struct clk *clk,
                                unsigned long prate)
{
    struct meson_vid_pll_div_data *data = (struct meson_vid_pll_div_data *)(clk->data);
    const struct vid_pll_div *div;
    uint32_t shift_val, shift_sel;

    shift_val = regmap_read_bits(data->val.reg_off, data->val.shift, data->val.width);
    shift_sel = regmap_read_bits(data->sel.reg_off, data->sel.shift, data->sel.width);

    int i;

    for (i = 0 ; i < ARRAY_SIZE(vid_pll_div_table) ; ++i) {
        if (vid_pll_div_table[i].shift_val == shift_val &&
            vid_pll_div_table[i].shift_sel == shift_sel) {
            div = &vid_pll_div_table[i];
            break;
        }
    }

    return DIV_ROUND_UP_ULL(prate * div->multiplier, div->divider);
}

const struct clk_ops meson_vid_pll_div_ro_ops = {
    .recalc_rate    = meson_vid_pll_div_recalc_rate,
};

static int meson_vclk_gate_enable(struct clk *clk)
{
    struct meson_vclk_gate_data *data = (struct meson_vclk_gate_data *)(clk->data);

    regmap_update_bits(data->enable.reg_off, data->enable.shift, data->enable.width, 1);

    /* Do a reset pulse */
    regmap_update_bits(data->reset.reg_off, data->reset.shift, data->reset.width, 1);
    regmap_update_bits(data->reset.reg_off, data->reset.shift, data->reset.width, 0);

    return 0;
}

static int meson_vclk_gate_disable(struct clk *clk)
{
    struct meson_vclk_gate_data *data = (struct meson_vclk_gate_data *)(clk->data);

    regmap_update_bits(data->enable.reg_off, data->enable.shift, data->enable.width, 0);
    return 0;
}

static int meson_vclk_gate_is_enabled(struct clk *clk)
{
    struct meson_vclk_gate_data *data = (struct meson_vclk_gate_data *)(clk->data);
    return regmap_read_bits(data->enable.reg_off, data->enable.shift, data->enable.width);
}

const struct clk_ops meson_vclk_gate_ops = {
    .enable = meson_vclk_gate_enable,
    .disable = meson_vclk_gate_disable,
    .is_enabled = meson_vclk_gate_is_enabled,
};

static unsigned long meson_vclk_div_recalc_rate(const struct clk *clk,
                                unsigned long prate)
{
    struct meson_vclk_div_data *data = (struct meson_vclk_div_data *)(clk->data);
    uint32_t div = regmap_read_bits(data->div.reg_off, data->div.shift, data->div.width);

    /* TODO: Need to verify the following cases */
    if (data->flags & CLK_DIVIDER_ONE_BASED) {
        ;
    } else if (data->flags & CLK_DIVIDER_POWER_OF_TWO) {
        div = 1 << div;
    } else if (data->flags & CLK_DIVIDER_MAX_AT_ZERO) {
        div = div ? div: MASK(data->div.width) + 1;
    } else {
        div += 1;
    }

    return DIV_ROUND_UP_ULL((uint64_t)prate, div);
}

static int meson_vclk_div_set_rate(const struct clk *clk, uint32_t rate, uint32_t parent_rate)
{
    struct meson_vclk_div_data *data = (struct meson_vclk_div_data *)(clk->data);

    uint32_t div = DIV_ROUND_UP(parent_rate, rate);

    if (data->flags & CLK_DIVIDER_ONE_BASED) {
        /* TODO: to be implemented */
        ;
    } else if (data->flags & CLK_DIVIDER_POWER_OF_TWO) {
        /* div = __ffs(div); */
    } else if (data->flags & CLK_DIVIDER_MAX_AT_ZERO) {
        div = (div == MASK(data->div.width) + 1) ? 0 : div;
    } else {
        div -= 1;
    }
    return regmap_update_bits(data->div.reg_off, data->div.shift, data->div.width, div);
}

static int meson_vclk_div_enable(struct clk *clk)
{
    struct meson_vclk_div_data *data = (struct meson_vclk_div_data *)(clk->data);

    regmap_update_bits(data->reset.reg_off, data->reset.shift, data->reset.width, 0);
    regmap_update_bits(data->enable.reg_off, data->enable.shift, data->enable.width, 1);

    return 0;
}

static int meson_vclk_div_disable(struct clk *clk)
{
    struct meson_vclk_div_data *data = (struct meson_vclk_div_data *)(clk->data);

    regmap_update_bits(data->enable.reg_off, data->enable.shift, data->enable.width, 0);
    regmap_update_bits(data->reset.reg_off, data->reset.shift, data->reset.width, 1);
    return 0;
}

static int meson_vclk_div_is_enabled(struct clk *clk)
{
    struct meson_vclk_div_data *data = (struct meson_vclk_div_data *)(clk->data);
    return regmap_read_bits(data->enable.reg_off, data->enable.shift, data->enable.width);
}

const struct clk_ops meson_vclk_div_ops = {
    .recalc_rate = meson_vclk_div_recalc_rate,
    /* .determine_rate = meson_vclk_div_determine_rate, */
    .set_rate = meson_vclk_div_set_rate,
    .enable = meson_vclk_div_enable,
    .disable = meson_vclk_div_disable,
    .is_enabled = meson_vclk_div_is_enabled,
};

const struct clk_ops meson_clk_cpu_dyndiv_ops = {
    /* .recalc_rate = meson_clk_cpu_dyndiv_recalc_rate, */
    /* .determine_rate = meson_clk_cpu_dyndiv_determine_rate, */
    /* .set_rate = meson_clk_cpu_dyndiv_set_rate, */
};
