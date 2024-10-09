/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Macros and data some structures are copied from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/include/linux/clk-provider.h
 *
 *  Copyright (c) 2010-2011 Jeremy Kerr <jeremy.kerr@canonical.com>
 *  Copyright (C) 2011-2012 Linaro Ltd <mturquette@linaro.org>
 */

/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Some data structures are derived from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/meson/clk-regmap.h
 *
 * Copyright (c) 2018 BayLibre, SAS.
 * Author: Jerome Brunet <jbrunet@baylibre.com>
 */

/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Some data structures are derived from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/meson/clk-pll.h
 *
 * Copyright (c) 2019 BayLibre, SAS.
 * Author: Jerome Brunet <jbrunet@baylibre.com>
 */

/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Some data structures are derived from:
 *   https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/meson/clk-mpll.h
 *
 * Copyright (c) 2019 BayLibre, SAS.
 * Author: Jerome Brunet <jbrunet@baylibre.com>
 */

/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Some data structures are derived from:
 *   https://github.com/torvalds/linux/blob/7ec462100ef9142344ddbf86f2c3008b97acddbe/drivers/clk/meson/vclk.h
 *
 * Copyright (c) 2024 Neil Armstrong <neil.armstrong@linaro.org>
 */

#ifndef CLK_PROVIDRE_H_
#define CLK_PROVIDER_H_

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
#define CLK_FRAC_DIVIDER_POWER_OF_TWO_PS   BIT(2)

#define BIT(nr) (1UL << (nr))

struct clk;

struct clk_hw {
    struct clk_core *core;
    struct clk *clk;
    struct clk_init_data *init;
};

struct clk_ops {
    uint8_t (*get_parent)(const struct clk *clk);
    int (*set_parent)(struct clk *clk, uint8_t index);
    unsigned long (*recalc_rate)(const struct clk *clk, unsigned long parent_rate);
    int (*set_rate)(const struct clk *clk, uint32_t rate, uint32_t parent_rate);
    void (*init)(struct clk *clk);
    int (*enable)(struct clk *clk);
    void (*disable)(struct clk *clk);
    int (*is_enabled)(struct clk *clk);
};

struct clk {
    struct clk_hw hw;
    void *data;
};

struct clk_core {
    /* struct clk_hw *hw; */
    uint32_t rate;          // TODO: Type?
};

struct clk_parent_data {
    const struct clk *clk;
    const char *fw_name;
    const char *name;
    int index;
};

struct clk_init_data {
    uint32_t num_parents;
    uint32_t flags;
    const char *name;
    const struct clk_ops *ops;
    const struct clk **parent_clks;
    const struct clk_parent_data *parent_data;
};

struct clk_gate_data {
    uint32_t offset;
    uint8_t bit_idx;
    uint8_t flags;
};

struct clk_div_table {

};

struct clk_source_data {
    uint64_t rate;
};
struct clk_div_data {
    uint32_t offset;
    uint8_t shift;
    uint8_t width;
    uint8_t flags;
    /* const struct clk_div_table *table; */
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

struct reg_sequence {
    unsigned int reg;
    unsigned int def;
    unsigned int delay_us;
};

struct pll_params_table {
    unsigned int    m;
    unsigned int    n;
};

#endif // CLK_PROVIDER_H_
