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
