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
#include <clk-measure.h> /* implementation of clock measurements */
#include <clk-meson.h> /* operations for meson-specific clocks */
#include <g12a-regs.h> /* offsets of control registers */
#include <g12a-bindings.h> /* clock id bindings*/

// Logging
/* #define DEBUG_DRIVER */

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("CLK DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("CLK DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define NUM_CLK_LIST CLKID_PCIE_PLL

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
            LOG_DRIVER("Initialise %s\n", clk_list[i]->hw.init->name);
        }
    }
}

const struct clk *get_parent(const struct clk *clk)
{
    if (!clk)
        return NULL;

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
int clk_get_rate(const struct clk *clk, uint64_t *rate)
{
    if (!clk)
        return CLK_UNKNOWN_TARGET;

    const struct clk_init_data *init = (struct clk_init_data *)clk->hw.init;
    uint64_t parent_rate = 0;
    int err = 0;

    const struct clk *parent_clk = get_parent(clk);
    if (parent_clk) {
        err = clk_get_rate(parent_clk, &parent_rate);
    }

    if (err)
        return err;

    *rate = parent_rate;
    if (init->ops->recalc_rate) {
        *rate = init->ops->recalc_rate(clk, parent_rate);
    }

    return 0;
}

int clk_enable(struct clk *clk)
{
    if (!clk)
        return CLK_UNKNOWN_TARGET;

    if (clk->hw.init->ops->enable != NULL) {
        return clk->hw.init->ops->enable(clk);
    }

    return CLK_INVALID_OP;
}

int clk_disable(struct clk *clk)
{
    if (!clk)
        return CLK_UNKNOWN_TARGET;

    if (clk->hw.init->ops->disable != NULL) {
        return clk->hw.init->ops->disable(clk);
    }

    return CLK_INVALID_OP;
}

int clk_set_rate(struct clk *clk, uint64_t req_rate, uint64_t *rate)
{
    if (!clk)
        return CLK_UNKNOWN_TARGET;

    /* TODO: we only propagate request to one level up. More operations need to be
     * invoked by clients until a dynamic configration algorithm implemented */
    if (clk->hw.init->ops->init) {
        clk->hw.init->ops->init(clk);
    }

    const struct clk *pclk = get_parent(clk);
    uint64_t prate = 0;
    int err = clk_get_rate(pclk, &prate);
    if (err) {
        LOG_DRIVER_ERR("Failed to get parent clock's rate\n");
        return err;
    }

    if (clk->hw.init->ops->set_rate) {
        clk->hw.init->ops->set_rate(clk, req_rate, prate);
        *rate = req_rate;
        return 0;
    }
    if (pclk->hw.init->ops->set_rate) {
        const struct clk *ppclk = get_parent(pclk);
        uint64_t pprate = 0;
        int err = clk_get_rate(ppclk, &pprate);
        if (!err) {
            pclk->hw.init->ops->set_rate(pclk, prate, pprate);
            *rate = req_rate;
            return 0;
        }
        return err;
    }

    return CLK_INVALID_OP;
}

int clk_msr_stat()
{
#ifdef DEBUG_DRIVER
    unsigned long clk_freq;
    int i = 0;
    uint64_t rate = 0;
    int err;

    const char *const *clk_msr_list = get_msr_clk_list();

    LOG_DRIVER("-------Expected clock rates------\n");
    for (i = 0; i < NUM_CLK_LIST; i++) {
        err = clk_get_rate(clk_list[i], &rate);
        if (err) {
            LOG_DRIVER("Failed to get rate of %s: -%u\n", clk_list[i]->hw.init->name, err);
        }
        LOG_DRIVER("[%4d][%4luHz] %s\n", i, rate, clk_list[i]->hw.init->name);
    }
    LOG_DRIVER("---------------------------------\n");
    LOG_DRIVER("---------Clock measurement-------\n");
    for (i = 0; i < 128; i++) {
        clk_freq = clk_msr(i);
        LOG_DRIVER("[%4d][%4ldHz] %s\n", i, clk_freq, clk_msr_list[i]);
    }
    LOG_DRIVER("-----------------------------\n");

#endif

    return 0;
}

void notified(microkit_channel ch)
{
}

void init(void)
{
    LOG_DRIVER("Clock driver initialising...\n");

    clk_list = get_clk_list();

    clk_probe(clk_list);
    clk_msr_stat();

    for (int i = 0; i < NUM_DEVICE_CLKS; i++) {
        struct clk *clk = clk_list[clk_configs[i].clk_id];

        /* Enable the clock */
        clk_enable(clk);

        /* TODO: Set parent */

        /* Set rate for the target clock */
        if (clk_configs[i].frequency > 0) {
            uint64_t rate = 0;
            int err = clk_set_rate(clk, clk_configs[i].frequency, &rate);
            if (err) {
                LOG_DRIVER_ERR("Failed to set rate [%d] for clk_id: %d\n", clk_configs[i].frequency,
                               clk_configs[i].clk_id);
            }
        }
    }
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    int err = 0;
    uint32_t ret_num = 0;
    uint32_t argc = microkit_msginfo_get_count(msginfo);

    /* TODO: Check if the channel is valid */
    switch (microkit_msginfo_get_label(msginfo)) {

    case SDDF_CLK_ENABLE: {
        if (argc != 1) {
            LOG_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            err = CLK_INCORRECT_ARGS;
            break;
        }
        uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
        LOG_DRIVER("get request clk_enable(%d)\n", clk_id);
        err = clk_enable(clk_list[clk_id]);
        break;
    }
    case SDDF_CLK_DISABLE: {
        if (argc != 1) {
            LOG_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            err = CLK_INCORRECT_ARGS;
            break;
        }
        uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
        LOG_DRIVER("get request clk_disable(%d)\n", clk_id);
        err = clk_disable(clk_list[clk_id]);
        break;
    }
    case SDDF_CLK_GET_RATE: {
        if (argc != 1) {
            LOG_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            err = CLK_INCORRECT_ARGS;
            break;
        }
        uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
        uint64_t rate = 0;
        err = clk_get_rate(clk_list[clk_id], &rate);
        microkit_mr_set(0, rate);
        ret_num = 1;
        break;
    }
    case SDDF_CLK_SET_RATE: {
        if (argc != 2) {
            LOG_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            err = CLK_INCORRECT_ARGS;
            break;
        }
        uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
        uint32_t req_rate = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_RATE);
        uint64_t rate = 0;
        err = clk_set_rate(clk_list[clk_id], req_rate, &rate);
        microkit_mr_set(0, rate);
        ret_num = 1;
        break;
    }
    default:
        LOG_DRIVER_ERR("Unknown request %lu to clockk driver from channel %u\n", microkit_msginfo_get_label(msginfo),
                       ch);
        err = CLK_UNKNOWN_REQ;
    }
    return microkit_msginfo_new(err, ret_num);
}
