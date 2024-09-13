/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <clk-operations.h>
#include <sddf/util/printf.h>

uintptr_t clk_base;

void init_clk_base(uintptr_t base_addr)
{
    clk_base = base_addr;
}

static inline int regmap_update_bits(uint32_t offset, uint8_t shift, uint8_t width, uint32_t val)
{
    sddf_dprintf("clk_base1: 0x%x\n", clk_base);
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

static inline int regmap_mux_read_bits(uint32_t offset, uint8_t shift, uint32_t mask)
{
    volatile uint32_t *clk_reg = ((void *)clk_base + offset);
    uint32_t reg_val = *clk_reg;

    reg_val >>= shift;
    reg_val &= mask;

    return reg_val;
}

static int clk_regmap_gate_enable(struct clk_hw *hw)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(hw->clk->data);

    return regmap_update_bits(data->offset, data->bit_idx, 1, 1);
}

static void clk_regmap_gate_disable(struct clk_hw *hw)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(hw->clk->data);

    regmap_update_bits(data->offset, data->bit_idx, 1, 0);
}

static int clk_regmap_gate_is_enabled(struct clk_hw *hw)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(hw->clk->data);

    /* TODO: to be checked */
    /* if (gate->flags & CLK_GATE_SET_TO_DISABLE) */
    /*     val ^= BIT(gate->bit_idx); */

    /* val &= BIT(gate->bit_idx); */
    /* return val ? 1 : 0; */

    return regmap_read_bits(data->offset, data->bit_idx, 1);
}

const struct clk_ops clk_regmap_gate_ops = {
    .enable = &clk_regmap_gate_enable,
    .disable = &clk_regmap_gate_disable,
    .is_enabled = clk_regmap_gate_is_enabled,
};

const struct clk_ops clk_regmap_gate_ro_ops = {
    .is_enabled = clk_regmap_gate_is_enabled,
};

static unsigned long clk_regmap_div_recalc_rate(struct clk_hw *hw,
                                unsigned long prate)
{

    struct clk_div_data *data = (struct clk_div_data *)(hw->clk->data);
    uint32_t div = regmap_read_bits(data->offset, data->shift, data->width);

    /* TODO: Need to verify the following cases */
    if (data->flags & CLK_DIVIDER_ONE_BASED) {
        div = div;
    } else if (data->flags & CLK_DIVIDER_POWER_OF_TWO) {
        div = 1 << div;
    } else if (data->flags & CLK_DIVIDER_MAX_AT_ZERO) {
        div = div ? div: MASK(data->width) + 1;
    } else if (data->table) {
        /* TODO: to be implemented */
        /* div = _get_table_div(table, val); */
    } else {
        div += 1;
    }

    return DIV_ROUND_UP_ULL((uint64_t)prate, div);
}

static int clk_regmap_div_set_rate(struct clk_hw *hw, uint32_t rate, uint32_t parent_rate)
{
    struct clk_div_data *data = (struct clk_div_data *)(hw->clk->data);
    uint32_t div = DIV_ROUND_UP(parent_rate, rate);

    if (data->flags & CLK_DIVIDER_ONE_BASED) {
        /* TODO: to be implemented */
        div = div;
    } else if (data->flags & CLK_DIVIDER_POWER_OF_TWO) {
        /* div = __ffs(div); */
    } else if (data->flags & CLK_DIVIDER_MAX_AT_ZERO) {
        div = (div == MASK(data->width) + 1) ? 0 : div;
    } else if (data->table) {
        /* TODO: to be implemented */
        /* return  _get_table_val(table, div); */
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
    .recalc_rate = clk_regmap_div_recalc_rate,
    /* .determine_rate = clk_regmap_div_determine_rate, */
    .set_rate = clk_regmap_div_set_rate,
};

const struct clk_ops clk_regmap_divider_ro_ops = {
    .recalc_rate = clk_regmap_div_recalc_rate,
    /* .determine_rate = clk_regmap_div_determine_rate, */
};

static uint8_t clk_regmap_mux_get_parent(struct clk_hw *hw)
{
    struct clk_mux_data *data = (struct clk_mux_data *)(hw->clk->data);
    uint32_t num_parents = hw->init->num_parents;
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

static struct clk_ops clk_regmap_mux_ops = {
    .get_parent = clk_regmap_mux_get_parent,
    /* .set_parent = clk_regmap_mux_set_parent, */
    /* .determine_rate = clk_regmap_mux_determine_rate, */
};

const struct clk_ops clk_regmap_mux_ro_ops = {
    .get_parent = clk_regmap_mux_get_parent,
};

static unsigned long clk_factor_recalc_rate(struct clk_hw *hw,
        unsigned long parent_rate)
{
    struct clk *clk = (struct clk *)(hw->clk);
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

static unsigned long meson_clk_pll_recalc_rate(struct clk_hw *hw,
                        unsigned long parent_rate)
{
    struct meson_clk_pll_data *data = (struct meson_clk_pll_data *)(hw->clk->data);
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
    sddf_dprintf("n = %lu, m = %lu, frac = %lu, rate = %lu\n", n, m, frac, rate);

    return DIV_ROUND_UP_ULL(rate, n);
}

const struct clk_ops meson_clk_pll_ro_ops = {
    .recalc_rate = meson_clk_pll_recalc_rate,
    /* .is_enabled    = meson_clk_pll_is_enabled, */
};
