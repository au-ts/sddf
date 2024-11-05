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

struct clk *get_clk_by_name(const char *name)
{
    for (int i = 0; i < NUM_CLK_LIST; i++) {
        if (clk_list[i] && sddf_strcmp(clk_list[i]->hw.init->name, name) == 0) {
            return clk_list[i];
        }
    }
    return NULL;
}

void clk_probe(struct clk *clk_list[])
{
    for (int i = 0; i < NUM_CLK_LIST; i++) {
        if (!clk_list[i]) {
            continue;
        }

        struct clk_init_data *init_data = clk_list[i]->hw.init;

        if (clk_list[i]->base == CCM_BASE) {
            clk_list[i]->base = ccm_base;
        } else if (clk_list[i]->base == CCM_ANALOG_BASE) {
            clk_list[i]->base = ccm_analog_base;
        }
        if (clk_list[i] && init_data->ops->init) {
            init_data->ops->init(clk_list[i]);
            LOG_DRIVER("Initialise %s\n", init_data->name);
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
        } else if (parent_data.name) {
            return get_clk_by_name(parent_data.name);
        }
    }

    if (num_parents > 0) {
        return init->parent_clks[0];
    }

    return NULL;
}

/* TODO: Should be just read from the structure, but need to update everytime when */
/*     related clocks are modified */
uint32_t clk_get_rate(const struct clk *clk, uint64_t *rate)
{
    if (!clk)
        return CLK_UNKNOWN_TARGET;

    const struct clk_init_data *init = (struct clk_init_data *)clk->hw.init;
    uint64_t parent_rate = 0;
    uint32_t err = 0;

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

uint32_t clk_enable(struct clk *clk)
{
    if (!clk)
        return CLK_UNKNOWN_TARGET;

    if (clk->hw.init->ops->enable != NULL) {
        return clk->hw.init->ops->enable(clk);
    }

    return CLK_INVALID_OP;
}

uint32_t clk_disable(struct clk *clk)
{
    if (!clk)
        return CLK_UNKNOWN_TARGET;

    if (clk->hw.init->ops->disable != NULL) {
        return clk->hw.init->ops->disable(clk);
    }

    return CLK_INVALID_OP;
}

uint32_t clk_set_rate(struct clk *clk, uint64_t req_rate, uint64_t *rate)
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
    uint32_t err = clk_get_rate(pclk, &prate);
    if (err) {
        LOG_DRIVER_ERR("Failed to get parent clock's rate\n");
        return err;
    }

    if (clk->hw.init->ops->set_rate) {
        *rate = clk->hw.init->ops->set_rate(clk, req_rate, prate);
        return 0;
    } else if (pclk && pclk->hw.init->ops->set_rate) {
        const struct clk *ppclk = get_parent(pclk);
        uint64_t pprate = 0;
        uint32_t err = clk_get_rate(ppclk, &pprate);
        if (!err) {
            pclk->hw.init->ops->set_rate(pclk, prate, pprate);
            return 0;
        }
        return err;
    }

    return CLK_INVALID_OP;
}

int clk_msr_stat()
{
#ifdef DEBUG_DRIVER
    int i;
    uint64_t rate = 0;
    uint32_t err;

    LOG_DRIVER("-------Expected clock rates------\n");
    for (i = 0; i < NUM_CLK_LIST; i++) {
        if (clk_list[i]) {
            err = clk_get_rate(clk_list[i], &rate);
            if (err) {
                LOG_DRIVER_ERR("Failed to get rate of %s: -%u\n", clk_list[i]->hw.init->name, err);
            }
            LOG_DRIVER("[%4d][%10luHz] %s\n", i, rate, clk_list[i]->hw.init->name);
        }
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
    clk_list = get_clk_list();

    clk_probe(clk_list);
    clk_msr_stat();

    for (int i = 0; i < NUM_DEVICE_CLKS; i++) {
        struct clk *clk = clk_list[clk_configs[i].clk_id];
        LOG_DRIVER("clk_id: %d\n", clk_configs[i].clk_id);
        /* Enable the clock */
        clk_enable(clk);

        /* TODO: Set parent */

        /* TODO: Set rate for the target clock */
        /* if (clk_configs[i].frequency > 0) { */
        /*     LOG_DRIVER("set rate for %s\n", clk->hw.init->name); */
        /*     uint64_t rate = 0; */
        /*     uint32_t err = clk_set_rate(clk, clk_configs[i].frequency, &rate); */
        /*     if (err) { */
        /*         LOG_DRIVER_ERR("Failed to set rate [%d] for clk_id: %d\n", clk_configs[i].frequency, clk_configs[i].clk_id); */
        /*     } */
        /*     LOG_DRIVER("------------------\n"); */
        /* } */
    }
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    uint32_t err = 0;
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
        break;
    }
    case SDDF_CLK_SET_RATE: {
        if (argc != 2) {
            LOG_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            err = CLK_INCORRECT_ARGS;
            break;
        }
        uint32_t clk_id = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_ID);
        uint64_t req_rate = (uint32_t)microkit_mr_get(SDDF_CLK_PARAM_RATE);
        uint64_t rate = 0;
        err = clk_set_rate(clk_list[clk_id], req_rate, &rate);
        break;
    }
    default:
        LOG_DRIVER_ERR("Unknown request %lu to clockk driver from channel %u\n",
                       microkit_msginfo_get_label(msginfo), ch);
        err = CLK_UNKNOWN_REQ;
    }
    return microkit_msginfo_new(err, 0);
}
