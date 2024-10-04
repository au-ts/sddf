// SPDX-License-Identifier: GPL-2.0+
/*
 * Amlogic Meson-G12A Clock Controller Driver
 *
 * Copyright (c) 2016 Baylibre SAS.
 * Author: Michael Turquette <mturquette@baylibre.com>
 *
 * Copyright (c) 2018 Amlogic, inc.
 * Author: Qiufang Dai <qiufang.dai@amlogic.com>
 * Author: Jian Hu <jian.hu@amlogic.com>
 *
 * Derived from: https://github.com/torvalds/linux/blob/befe87380e21f0d37633273e1068c9318f8135ff/drivers/clk/meson/g12a.c
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/util/string.h>
#include <sddf/util/printf.h>
#include <clk_config.h>

/* Test for Odroid-C4 */
#include <clk.h>
#include <clk-operations.h>
#include <clk-measure.h>
#include <g12a.h>
#include <g12a-clkc.h>
#include <conf_types.h>
#include <sm1_clk_hws.h>

#define I2C_CLK_OFFSET 320
#define I2C_CLK_BIT (1 << 9) // bit 9

uintptr_t clk_regs;
uintptr_t msr_clk_base;

/* TODO: Should be configured with init_regs */
/* static struct clk_cfg fixed_clk_configs[] = { */
/*     { .clk_id = CLKID_FCLK_DIV2_DIV, .frequency = 1000000000 }, */
/*     { .clk_id = CLKID_FCLK_DIV3_DIV, .frequency = 666666667 }, */
/*     { .clk_id = CLKID_FCLK_DIV4_DIV, .frequency = 500000000 }, */
/*     { .clk_id = CLKID_FCLK_DIV5_DIV, .frequency = 400000000 }, */
/*     { .clk_id = CLKID_FCLK_DIV7_DIV, .frequency = 285700000 }, */
/* } */

void clk_init(struct clk *sm1_clks[])
{
    int i;
    for (i = 0; i < CLKID_PCIE_PLL; i++) {
        if (sm1_clks[i] && sm1_clks[i]->hw.init->ops->init) {
            sm1_clks[i]->hw.init->ops->init(sm1_clks[i]);
            sddf_dprintf("Initialise %s\n", sm1_clks[i]->hw.init->name);
        }
    }
}

const struct clk *get_parent(const struct clk *clk)
{
    const struct clk_init_data *init = (struct clk_init_data *)clk->hw.init;
    uint32_t num_parents = init->num_parents;

    if (init->parent_data) {
        uint8_t parent_idx = num_parents > 1 ? init->ops->get_parent(clk) : 0;
        struct clk_parent_data parent_data = init->parent_data[parent_idx];

        if (parent_data.clk) {
            return parent_data.clk;
        } else if (sddf_strcmp(parent_data.fw_name, "xtal") == 0) {
            return &g12a_xtal;
        }
    }

    if (num_parents > 0) {
        return init->parent_clks[0];
    }

    return NULL;
}

unsigned long clk_recalc_rate(const struct clk *clk)
{
    const struct clk_init_data *init = (struct clk_init_data *)clk->hw.init;
    unsigned long parent_rate = 0;

    const struct clk *parent_clk = get_parent(clk);
    if (parent_clk) {
        parent_rate = clk_recalc_rate(parent_clk);
    }

    unsigned long rate = parent_rate;
    if (init->ops->recalc_rate) {
        rate = init->ops->recalc_rate(clk, parent_rate);
    }

    return rate;
}

void enable_clk(struct clk *clk)
{
    sddf_dprintf("enable %s, 0x%x\n", clk->hw.init->name, clk->hw.init->ops);
    if (clk->hw.init->ops->enable != NULL) {
        clk->hw.init->ops->enable(clk);
    }
    sddf_dprintf("Done\n");
}

void set_clk_rate(struct clk *clk, uint32_t rate)
{
    if (clk->hw.init->ops->init) {
        clk->hw.init->ops->init(clk);
    }

    if (clk->hw.init->ops->set_rate) {
        /* determine_rate() needs to be implemented */
        const struct clk *parent_clk = get_parent(clk);
        uint64_t prate = clk_recalc_rate(parent_clk);
        sddf_dprintf("set %s to %dHz\n", clk->hw.init->name, rate);
        clk->hw.init->ops->set_rate(clk, rate, prate);
    }
}

void notified(microkit_channel ch)
{

}

void init(void)
{
    struct clk **sm1_clks = get_clk_list();
    init_clk_base(clk_regs);
    clk_init(sm1_clks);

    sddf_dprintf("-----------------\n");
    volatile uint32_t *clk_i2c_ptr = ((void *)clk_regs + I2C_CLK_OFFSET);

    sddf_dprintf("Clock driver initialising...\n");

    for (int i = 0; i < NUM_DEVICE_CLKS; i++) {
        struct clk *clk = sm1_clks[clk_configs[i].clk_id];

        /* Enable the clock */
        enable_clk(clk);

        /* TODO: Set parent */

        /* Set rate for the target clock */
        if (clk_configs[i].frequency > 0) {
            set_clk_rate(clk, clk_configs[i].frequency);
        }
    }

    // Check that registers actually changed
    if (!(*clk_i2c_ptr & I2C_CLK_BIT)) {
        sddf_dprintf("failed to toggle clock!\n");
    }

    sddf_dprintf("-----------------\n");

    struct clk *mpeg_sel = sm1_clks[CLKID_MPEG_SEL];
    uint64_t rate = clk_recalc_rate(mpeg_sel);
    sddf_dprintf("MEPG_SEL clock rate: %lu\n", rate);

    /* /\*     CLKID_MPLL2    0x11940000 *\/ */
    /* /\*     CLKID_MPLL0    0x10266000 *\/ */
    /* /\*     CLKID_MPLL1    0x17700000 *\/ */
    struct clk *parent_clk = sm1_clks[CLKID_MPLL_PREDIV];
    uint64_t prate = clk_recalc_rate(parent_clk);
    sddf_dprintf("%s rate: %lu\n", parent_clk->hw.init->name, rate);

    struct clk *mpll0_clk = sm1_clks[CLKID_MPLL0_DIV];
    mpll0_clk->hw.init->ops->set_rate(mpll0_clk, 0x10266000, prate);
    rate = clk_recalc_rate(mpll0_clk);
    sddf_dprintf("%s rate: %lu\n", mpll0_clk->hw.init->name, rate);

    struct clk *mpll1_clk = sm1_clks[CLKID_MPLL1_DIV];
    mpll1_clk->hw.init->ops->set_rate(mpll1_clk, 0x17700000, prate);
    rate = clk_recalc_rate(mpll1_clk);
    sddf_dprintf("%s rate: %lu\n", mpll1_clk->hw.init->name, rate);

    struct clk *mpll2_clk = sm1_clks[CLKID_MPLL2_DIV];
    mpll2_clk->hw.init->ops->set_rate(mpll2_clk, 0x11940000, prate);
    rate = clk_recalc_rate(mpll2_clk);
    sddf_dprintf("%s rate: %lu\n", mpll2_clk->hw.init->name, rate);

    clk_msr_stat();

    sddf_dprintf("-----------------\n");
}
