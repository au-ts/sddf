/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/clk/protocol.h>

/**
 * Send a clock enabling request via PPC into the passive clock driver.
 * Use the label to indicate this request.
 * @param channel of clock driver.
 * @param identifier of target clock.
 */
static inline int sddf_clk_enable(microkit_channel channel, uint32_t clk_id)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_ENABLE, 1);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Send a clock disabling request via PPC into the passive clock driver.
 * Use the label to indicate this request.
 * @param channel of clock driver.
 * @param identifier of target clock.
 */
static inline int sddf_clk_disable(microkit_channel channel, uint32_t clk_id)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_DISABLE, 1);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Send a clock get_rate request via PPC into the passive clock driver.
 * Use the label to indicate this request.
 * @param channel of clock driver.
 * @param identifier of target clock.
 * @param pointer to result variable.
 */
static inline int sddf_clk_get_rate(microkit_channel channel, uint32_t clk_id, uint64_t *rate)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_GET_RATE, 1);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);

    msginfo = microkit_ppcall(channel, msginfo);

    *rate = microkit_mr_get(0);
    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Send a clock set_rate request via PPC into the passive clock driver.
 * Use the label to indicate this request.
 * @param channel of clock driver.
 * @param identifier of target clock.
 * @param target clock frequency.
 * @param pointer to result variable.
 */
static inline int sddf_clk_set_rate(microkit_channel channel, uint32_t clk_id, uint64_t req_rate, uint64_t *rate)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_SET_RATE, 2);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);
    microkit_mr_set(SDDF_CLK_PARAM_RATE, req_rate);

    msginfo = microkit_ppcall(channel, msginfo);

    *rate = microkit_mr_get(0);
    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Send a clock get_parent request via PPC into the passive clock driver.
 * Use the label to indicate this request.
 * @param channel of clock driver.
 * @param pointer to result (i.e. pclk_id)
 */
static inline int sddf_clk_get_parent(microkit_channel channel, uint32_t clk_id, uint32_t *pclk_id)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_GET_PARENT, 1);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);

    msginfo = microkit_ppcall(channel, msginfo);

    *pclk_id = microkit_mr_get(0);
    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Send a clock set_parent request via PPC into the passive clock driver.
 * Use the label to indicate this request.
 * @param channel of clock driver.
 * @param identifier of target clock.
 * @param indice of target clock.
 */
static inline int sddf_clk_set_parent(microkit_channel channel, uint32_t clk_id, uint32_t parent_idx)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_SET_PARENT, 2);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);
    microkit_mr_set(SDDF_CLK_PARAM_PCLK_IDX, parent_idx);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}
