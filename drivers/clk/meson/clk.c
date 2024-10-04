/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
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

// Logging
#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("CLK DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("CLK DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

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
            LOG_DRIVER("Initialise %s\n", sm1_clks[i]->hw.init->name);
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
    LOG_DRIVER("enable %s, 0x%x\n", clk->hw.init->name, clk->hw.init->ops);
    if (clk->hw.init->ops->enable != NULL) {
        clk->hw.init->ops->enable(clk);
    }
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
        LOG_DRIVER("set %s to %dHz\n", clk->hw.init->name, rate);
        clk->hw.init->ops->set_rate(clk, rate, prate);
    }
}

int clk_msr_stat()
{
    unsigned long clk_freq;
    int i = 0;

    char **clk_msr_list = get_msr_clk_list();
    for (i = 0; i < 128; i++) {
        clk_freq = clk_msr(i);
        LOG_DRIVER("[%4d][%4ldHz] %s\n", i, clk_freq, clk_msr_list[i]);
    }

    return 0;
}

void notified(microkit_channel ch)
{

}

void init(void)
{
    LOG_DRIVER("Clock driver initialising...\n");
    struct clk **sm1_clks = get_clk_list();
    init_clk_base(clk_regs);
    clk_init(sm1_clks);

    volatile uint32_t *clk_i2c_ptr = ((void *)clk_regs + I2C_CLK_OFFSET);


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
        LOG_DRIVER_ERR("failed to toggle clock!\n");
    }

    clk_msr_stat();
}
