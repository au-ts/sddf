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
static inline uint32_t sddf_clk_enable(microkit_channel channel, uint32_t clk_id)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_ENABLE, 1);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);

    msginfo = microkit_ppcall(channel, msginfo);

    return (uint32_t)microkit_msginfo_get_label(msginfo);
}

/**
 * Send a clock disabling request via PPC into the passive clock driver.
 * Use the label to indicate this request.
 * @param channel of clock driver.
 * @param identifier of target clock.
 */
static inline uint32_t sddf_clk_disable(microkit_channel channel, uint32_t clk_id)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_DISABLE, 1);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);

    msginfo = microkit_ppcall(channel, msginfo);

    return (uint32_t)microkit_msginfo_get_label(msginfo);
}

/**
 * Send a clock get_rate request via PPC into the passive clock driver.
 * Use the label to indicate this request.
 * @param channel of clock driver.
 * @param identifier of target clock.
 */
static inline uint32_t sddf_clk_get_rate(microkit_channel channel, uint32_t clk_id)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_GET_RATE, 1);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);

    msginfo = microkit_ppcall(channel, msginfo);

    return (uint32_t)microkit_msginfo_get_label(msginfo);
}

/**
 * Send a clock set_rate request via PPC into the passive clock driver.
 * Use the label to indicate this request.
 * @param channel of clock driver.
 * @param identifier of target clock.
 * @param target clock frequency.
 */
static inline uint32_t sddf_clk_set_rate(microkit_channel channel, uint32_t clk_id, uint32_t rate)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_SET_RATE, 2);
    microkit_mr_set(SDDF_CLK_PARAM_ID, clk_id);
    microkit_mr_set(SDDF_CLK_PARAM_RATE, rate);

    msginfo = microkit_ppcall(channel, msginfo);

    return (uint32_t)microkit_msginfo_get_label(msginfo);
}

/**
 * @TODO: This is a temporary solution to intercept reuqests from driver VMMs
 *
 * VMM can use this interface to process unmatched writes
 *
 * @param channel of clock driver.
 * @param addr offset of the write operation.
 * @param value that the driver vm tries to write.
 */
static inline uint32_t sddf_clk_handle_request(microkit_channel channel, uint32_t paddr, uint32_t value)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_CLK_HANDLE_REQUEST, 2);
    microkit_mr_set(SDDF_CLK_PARAM_PADDR, paddr);
    microkit_mr_set(SDDF_CLK_PARAM_VALUE, value);

    msginfo = microkit_ppcall(channel, msginfo);

    return (uint32_t)microkit_msginfo_get_label(msginfo);
}
