/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Terry Bai: tianyi.bai@unsw.edu.au
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/util/string.h>
#include <sddf/util/printf.h>
#include <sddf/clk/protocol.h>
#include <clk_config.h>

#include <clk.h>            /* common definitions and interfaces */
#include <clk-operations.h> /* ops of common clocks e.g., div, mux, fixed factor, and gate*/
#include <clk-measure.h>    /* implementation of clock measurements */
#include <clk-meson.h>      /* operations for meson-specific clocks */
#include <g12a-regs.h>      /* offsets of control registers */
#include <g12a-bindings.h>  /* clock id bindings*/

// Logging
#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_CLK(...) do{ sddf_dprintf("CLK DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_CLK(...) do{}while(0)
#endif

#define LOG_CLK_ERR(...) do{ sddf_printf("CLK DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define NUM_CLK_LIST CLKID_PCIE_PLL
#define CLK_PHYS_BASE 0xff63c000

#define I2C_CLK_OFFSET 320
#define I2C_CLK_BIT (1 << 9) // bit 9

uintptr_t clk_regs;
uintptr_t msr_clk_base;

struct clk **clk_list;

/* TODO: Should be configured with init_regs */
/* static struct clk_cfg fixed_clk_configs[] = { */
/*     { .clk_id = CLKID_FCLK_DIV2_DIV, .frequency = 1000000000 }, */
/*     { .clk_id = CLKID_FCLK_DIV3_DIV, .frequency = 666666667 }, */
/*     { .clk_id = CLKID_FCLK_DIV4_DIV, .frequency = 500000000 }, */
/*     { .clk_id = CLKID_FCLK_DIV5_DIV, .frequency = 400000000 }, */
/*     { .clk_id = CLKID_FCLK_DIV7_DIV, .frequency = 285700000 }, */
/* } */

void clk_probe(struct clk *clk_list[])
{
    int i;
    for (i = 0; i < NUM_CLK_LIST; i++) {
        clk_list[i]->base = (uint64_t)clk_regs;
        if (clk_list[i] && clk_list[i]->hw.init->ops->init) {
            clk_list[i]->hw.init->ops->init(clk_list[i]);
            LOG_CLK("Initialise %s\n", clk_list[i]->hw.init->name);
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
        } else if (sddf_strcmp(parent_data.name, "xtal") == 0) {
            return &g12a_xtal;
        }
    }

    if (num_parents > 0) {
        return init->parent_clks[0];
    }

    return NULL;
}

/* TODO: Should be just read from the structure, but need to update everytime when */
/*     related clocks are modified */
unsigned long clk_get_rate(const struct clk *clk)
{
    const struct clk_init_data *init = (struct clk_init_data *)clk->hw.init;
    unsigned long parent_rate = 0;

    const struct clk *parent_clk = get_parent(clk);
    if (parent_clk) {
        parent_rate = clk_get_rate(parent_clk);
    }

    unsigned long rate = parent_rate;
    if (init->ops->recalc_rate) {
        rate = init->ops->recalc_rate(clk, parent_rate);
    }

    return rate;
}

uint32_t clk_enable(struct clk *clk)
{
    if (clk->hw.init->ops->enable != NULL) {
        return clk->hw.init->ops->enable(clk);
    }

    return CLK_INVALID_OP;
}

uint32_t clk_disable(struct clk *clk)
{
    if (clk->hw.init->ops->disable != NULL) {
        return clk->hw.init->ops->disable(clk);
    }

    return CLK_INVALID_OP;
}

uint32_t clk_set_rate(struct clk *clk, uint32_t rate)
{
    if (clk->hw.init->ops->init) {
        clk->hw.init->ops->init(clk);
    }

    const struct clk *pclk = get_parent(clk);
    uint64_t prate = clk_get_rate(pclk);
    if (clk->hw.init->ops->set_rate) {
        /* TODO: determine_rate() needs to be implemented */
        LOG_CLK("set %s to %dHz\n", clk->hw.init->name, rate);
        clk->hw.init->ops->set_rate(clk, rate, prate);
    } else {
        /* TODO: We only propagate one level right now */
        if (pclk->hw.init->ops->set_rate) {
            const struct clk *ppclk = get_parent(pclk);
            uint64_t pprate = clk_get_rate(ppclk);
            /* TODO: determine_rate() needs to be implemented */
            LOG_CLK("set %s to %dHz\n", pclk->hw.init->name, rate);
            pclk->hw.init->ops->set_rate(pclk, prate, pprate);
        }
    }

    return 0;
}

/* TODO: This is a hacky function that only handles enabling gate request */
uint32_t clk_handle_request(microkit_channel ch, uint32_t phys_addr, uint32_t val)
{
    uint32_t offset = phys_addr - CLK_PHYS_BASE;
    LOG_CLK("write 0x%x to 0x%x---\n", val, phys_addr);
    if (ch == 2) {
        if ((offset >= 0x3a0 && offset < 0x3a8) ||
            (offset >= 0x320 && offset < 0x33b) ||
            (offset >= 0x2f4 && offset < 0x2f8) ||
            (offset >= 0x1b0 && offset < 0x1b4) ||
            (offset >= 0x19c && offset < 0x1a4)) {
            LOG_CLK("write 0x%x to 0x%x\n", val, phys_addr);
            reg_write(clk_regs, offset, val);
        }
    }

    return 0;
}

int clk_msr_stat()
{
    unsigned long clk_freq;
    int i = 0;

    const char *const *clk_msr_list = get_msr_clk_list();
    for (i = 0; i < 128; i++) {
        clk_freq = clk_msr(i);
        LOG_CLK("[%4d][%4ldHz] %s\n", i, clk_freq, clk_msr_list[i]);
    }

    return 0;
}

void notified(microkit_channel ch)
{

}

void init(void)
{
    LOG_CLK("Clock driver initialising...\n");

    clk_list = get_clk_list();

    clk_probe(clk_list);

    volatile uint32_t *clk_i2c_ptr = ((void *)clk_regs + I2C_CLK_OFFSET);


    for (int i = 0; i < NUM_DEVICE_CLKS; i++) {
        struct clk *clk = clk_list[clk_configs[i].clk_id];

        /* Enable the clock */
        clk_enable(clk);

        /* TODO: Set parent */

        /* Set rate for the target clock */
        if (clk_configs[i].frequency > 0) {
            clk_set_rate(clk, clk_configs[i].frequency);
        }
    }

    // Check that registers actually changed
    if (!(*clk_i2c_ptr & I2C_CLK_BIT)) {
        LOG_CLK_ERR("failed to toggle clock!\n");
    }

    /* clk_msr_stat(); */
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    uint32_t ret = 0;
    uint32_t argc = microkit_msginfo_get_count(msginfo);

    /* TODO: Check if the channel is valid */
    switch (microkit_msginfo_get_label(msginfo)) {

        case SDDF_CLK_ENABLE: {
            if (argc != 1) {
                LOG_CLK_ERR("Incorrect number of arguments %u != 1\n", argc);
                ret = CLK_INCORRECT_ARGS;
                break;
            }
            uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
            LOG_CLK("get request clk_enable(%d)\n", clk_id);
            ret = clk_enable(clk_list[clk_id]);
            break;
        }
        case SDDF_CLK_DISABLE: {
            if (argc != 1) {
                LOG_CLK_ERR("Incorrect number of arguments %u != 1\n", argc);
                ret = CLK_INCORRECT_ARGS;
                break;
            }
            uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
            LOG_CLK("get request clk_disable(%d)\n", clk_id);
            ret = clk_disable(clk_list[clk_id]);
            break;
        }
        case SDDF_CLK_GET_RATE: {
            if (argc != 1) {
                LOG_CLK_ERR("Incorrect number of arguments %u != 1\n", argc);
                ret = CLK_INCORRECT_ARGS;
                break;
            }
            uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
            ret = clk_get_rate(clk_list[clk_id]);
            break;
        }
        case SDDF_CLK_SET_RATE: {
            if (argc != 2) {
                LOG_CLK_ERR("Incorrect number of arguments %u != 1\n", argc);
                ret = CLK_INCORRECT_ARGS;
                break;
            }
            uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
            uint32_t rate = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_RATE);
            ret = clk_set_rate(clk_list[clk_id], rate);
            break;
        }
        case SDDF_CLK_HANDLE_REQUEST: {
            if (argc != 2) {
                LOG_CLK_ERR("Incorrect number of arguments %u != 1\n", argc);
                ret = CLK_INCORRECT_ARGS;
                break;
            }
            uint32_t phys_addr = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_PADDR);
            uint32_t val = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_VALUE);
            ret = clk_handle_request(ch, phys_addr, val);
            break;
        }
        default:
            LOG_CLK_ERR("Unknown request %lu to clockk driver from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
            ret = 5;
    }
    return microkit_msginfo_new(ret, 0);
}
