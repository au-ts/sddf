/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifndef CLK_H_
#define CLK_H_

#include <stdint.h>

#define CLK_SET_RATE_GATE    BIT(0) /* must be gated across rate change */
#define CLK_SET_PARENT_GATE    BIT(1) /* must be gated across re-parent */
#define CLK_SET_RATE_PARENT    BIT(2) /* propagate rate change up one level */
#define CLK_IGNORE_UNUSED    BIT(3) /* do not gate even if unused */
                /* unused */
                /* unused */
#define CLK_GET_RATE_NOCACHE    BIT(6) /* do not use the cached clk rate */
#define CLK_SET_RATE_NO_REPARENT BIT(7) /* don't re-parent on rate change */
#define CLK_GET_ACCURACY_NOCACHE BIT(8) /* do not use the cached clk accuracy */
#define CLK_RECALC_NEW_RATES    BIT(9) /* recalc rates after notifications */
#define CLK_SET_RATE_UNGATE    BIT(10) /* clock needs to run to set rate */
#define CLK_IS_CRITICAL        BIT(11) /* do not gate, ever */
/* parents need enable during gate/ungate, set rate and re-parent */
#define CLK_OPS_PARENT_ENABLE    BIT(12)
/* duty cycle call may be forwarded to the parent clock */
#define CLK_DUTY_CYCLE_PARENT    BIT(13)

#define CLK_GATE_SET_TO_DISABLE        BIT(0)
#define CLK_GATE_HIWORD_MASK        BIT(1)
#define CLK_GATE_BIG_ENDIAN        BIT(2)

#define CLK_DIVIDER_ONE_BASED        BIT(0)
#define CLK_DIVIDER_POWER_OF_TWO    BIT(1)
#define CLK_DIVIDER_ALLOW_ZERO        BIT(2)
#define CLK_DIVIDER_HIWORD_MASK        BIT(3)
#define CLK_DIVIDER_ROUND_CLOSEST    BIT(4)
#define CLK_DIVIDER_READ_ONLY        BIT(5)
#define CLK_DIVIDER_MAX_AT_ZERO        BIT(6)
#define CLK_DIVIDER_BIG_ENDIAN        BIT(7)

#define CLK_MUX_INDEX_ONE        BIT(0)
#define CLK_MUX_INDEX_BIT        BIT(1)
#define CLK_MUX_HIWORD_MASK        BIT(2)
#define CLK_MUX_READ_ONLY        BIT(3) /* mux can't be changed */
#define CLK_MUX_ROUND_CLOSEST        BIT(4)
#define CLK_MUX_BIG_ENDIAN        BIT(5)

#define CLK_FRAC_DIVIDER_ZERO_BASED        BIT(0)
#define CLK_FRAC_DIVIDER_BIG_ENDIAN        BIT(1)
#define CLK_FRAC_DIVIDER_POWER_OF_TWO_PS    BIT(2)

#define BIT(nr) (1UL << (nr))

struct clk;

struct clk_hw {
    struct clk_core *core;
    struct clk *clk;
    struct clk_init_data *init;
};


struct clk_ops {
    uint8_t (*get_parent)(struct clk_hw *hw);
    int (*set_parent)(struct clk_hw *hw, uint8_t index);
    unsigned long (*recalc_rate)(struct clk_hw *hw, unsigned long parent_rate);
    int (*set_rate)(struct clk_hw *hw, uint32_t rate, uint32_t parent_rate);
    int (*enable)(struct clk_hw *hw);
    void (*disable)(struct clk_hw *hw);
    int (*is_enabled)(struct clk_hw *hw);
};

struct clk {
    struct clk_hw hw;
    void *data;
};

struct clk_core {
    /* struct clk_hw *hw; */
    uint32_t rate;          // TODO: Type?
};

/**
 * struct clk_parent_data - clk parent information
 * @hw: parent clk_hw pointer (used for clk providers with internal clks)
 * @fw_name: parent name local to provider registering clk
 * @name: globally unique parent name (used as a fallback)
 * @index: parent index local to provider registering clk (if @fw_name absent)
 */
struct clk_parent_data {
    const struct clk_hw *hw;
    const char *fw_name;
    const char *name;
    int index;
};

struct clk_init_data {
    uint32_t num_parents;
    uint32_t flags;
    const char *name;
    const struct clk_ops *ops;
    const struct clk_hw **parent_hws;
    const struct clk_parent_data *parent_data;
};

struct clk_gate_data {
    uint32_t offset;
    uint8_t bit_idx;
    uint8_t flags;
};

struct clk_div_table {

};

struct clk_div_data {
    uint32_t offset;
    uint8_t shift;
    uint8_t width;
    uint8_t flags;
    const struct clk_div_table *table;
};

struct clk_fixed_factor_data {
    uint32_t mult;
    uint32_t div;
};

struct clk_mux_data {
    uint32_t offset;
    uint32_t *table;
    uint32_t mask;
    uint8_t shift;
    uint8_t flags;
};

struct parm {
    uint16_t reg_off;
    uint8_t shift;
    uint8_t width;
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
    /* const struct reg_sequence *init_regs; */
    unsigned int init_count;
    /* const struct pll_params_table *table; */
    /* const struct pll_mult_range *range; */
    uint8_t flags;
};

/**
 * struct clk_rate_request - Structure encoding the clk constraints that
 * a clock user might require.
 *
 * Should be initialized by calling clk_hw_init_rate_request().
 *
 * @core:           Pointer to the struct clk_core affected by this request
 * @rate:           Requested clock rate. This field will be adjusted by
 *                    clock drivers according to hardware capabilities.
 * @min_rate:        Minimum rate imposed by clk users.
 * @max_rate:        Maximum rate imposed by clk users.
 * @best_parent_rate:    The best parent rate a parent can provide to fulfill the
 *            requested constraints.
 * @best_parent_hw:    The most appropriate parent clock that fulfills the
 *            requested constraints.
 *
 */
struct clk_rate_request {
    struct clk_core *core;
    unsigned long rate;
    unsigned long min_rate;
    unsigned long max_rate;
    unsigned long best_parent_rate;
    struct clk_hw *best_parent_hw;
};

#endif // CLK_H_
