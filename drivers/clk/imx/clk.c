/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Terry Bai: tianyi.bai@unsw.edu.au
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>
#include <sddf/clk/protocol.h>

#include <clk.h>
#include <clk-imx.h>
#include <clk-operations.h>
#include <clk_config.h>
#include <imx8mq-bindings.h>

// Logging
/* #define DEBUG_DRIVER */

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("CLK DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("CLK DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define CLIENT_CH 0

#define NUM_CLK_LIST IMX8MQ_CLK_END

struct clk **clk_list;

uintptr_t ccm_base;
uintptr_t ccm_analog_base;

void clk_probe(struct clk *clk_list[])
{
    int i;
    for (i = 0; i < NUM_CLK_LIST; i++) {
        if (!clk_list[i]) {
            continue;
        }
        if (clk_list[i]->base == CCM_BASE) {
            clk_list[i]->base = ccm_base;
        } else if (clk_list[i]->base == CCM_ANALOG_BASE) {
            clk_list[i]->base = ccm_analog_base;
        }
        if (clk_list[i] && clk_list[i]->hw.init->ops->init) {
            clk_list[i]->hw.init->ops->init(clk_list[i]);
            LOG_DRIVER("Initialise %s\n", clk_list[i]->hw.init->name);
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
            return NULL;
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
        LOG_DRIVER("set %s to %dHz\n", clk->hw.init->name, rate);
        clk->hw.init->ops->set_rate(clk, rate, prate);
    } else {
        /* TODO: We only propagate one level right now */
        if (pclk->hw.init->ops->set_rate) {
            const struct clk *ppclk = get_parent(pclk);
            uint64_t pprate = clk_get_rate(ppclk);
            /* TODO: determine_rate() needs to be implemented */
            LOG_DRIVER("set %s to %dHz\n", pclk->hw.init->name, rate);
            pclk->hw.init->ops->set_rate(pclk, prate, pprate);
        }
    }

    return 0;
}

void notified(microkit_channel ch)
{
}

void init(void)
{

    clk_list = get_clk_list();

    clk_probe(clk_list);

    for (int i = 0; i < NUM_DEVICE_CLKS; i++) {
        uint32_t idx = clk_configs[i].clk_id;
        uint32_t rate = clk_configs[i].frequency;

        sddf_dprintf("idx: %u, frequency: 0x%x\n", idx, rate);
    }
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    uint32_t ret = 0;
    uint32_t argc = microkit_msginfo_get_count(msginfo);

    /* TODO: Check if the channel is valid */
    switch (microkit_msginfo_get_label(msginfo)) {

    case SDDF_CLK_ENABLE: {
        if (argc != 1) {
            LOG_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            ret = CLK_INCORRECT_ARGS;
            break;
        }
        uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
        LOG_DRIVER("get request clk_enable(%d)\n", clk_id);
        ret = clk_enable(clk_list[clk_id]);
        break;
    }
    case SDDF_CLK_DISABLE: {
        if (argc != 1) {
            LOG_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            ret = CLK_INCORRECT_ARGS;
            break;
        }
        uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
        LOG_DRIVER("get request clk_disable(%d)\n", clk_id);
        ret = clk_disable(clk_list[clk_id]);
        break;
    }
    case SDDF_CLK_GET_RATE: {
        if (argc != 1) {
            LOG_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            ret = CLK_INCORRECT_ARGS;
            break;
        }
        uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
        ret = clk_get_rate(clk_list[clk_id]);
        break;
    }
    case SDDF_CLK_SET_RATE: {
        if (argc != 2) {
            LOG_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            ret = CLK_INCORRECT_ARGS;
            break;
        }
        uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
        uint32_t rate = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_RATE);
        ret = clk_set_rate(clk_list[clk_id], rate);
        break;
    }
    default:
        LOG_DRIVER_ERR("Unknown request %lu to clockk driver from channel %u\n", microkit_msginfo_get_label(msginfo),
                       ch);
        ret = 5;
    }
    return microkit_msginfo_new(ret, 0);
}
