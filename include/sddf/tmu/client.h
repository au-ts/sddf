/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/tmu/protocol.h>

/**
 * Set the IRQ forwarding mode via PPC to the passive TMU driver.
 * @param channel of TMU driver.
 * @param mode IRQ mode (disabled, instantaneous, or average).
 * @return 0 on success, 1 on failure.
 */
static inline int sddf_tmu_set_irq_mode(microkit_channel channel, sddf_tmu_irq_modes_t mode)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_TMU_SET_IRQ_MODE, 1);
    microkit_mr_set(SDDF_TMU_SET_IRQ_MODE_MODE, mode);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Set the high temperature threshold for IRQ delivery via PPC to the passive TMU driver.
 * @param channel of TMU driver.
 * @param threshold high temperature threshold in degrees celsius.
 * @return 0 on success, 1 on failure.
 */
static inline int sddf_tmu_set_irq_threshold(microkit_channel channel, int64_t threshold)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_TMU_SET_IRQ_THRESHOLD, 1);
    microkit_mr_set(0, threshold);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Get temperature readings from the TMU via PPC to the passive TMU driver.
 * @param channel of TMU driver.
 * @param info pointer to structure to populate with temperature data.
 * @return 0 on success, 1 on failure.
 */
static inline int sddf_tmu_get_temp(microkit_channel channel, sddf_tmu_temp_info_t *info)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_TMU_GET_TEMP, 0);

    msginfo = microkit_ppcall(channel, msginfo);

    int ret = (int)microkit_msginfo_get_label(msginfo);
    if (ret == SDDF_TMU_ERR_OK) {
        uint64_t valid = microkit_mr_get(SDDF_TMU_GET_TEMP_VALIDITY);
        info->valid_inst = valid & 0b1;
        info->valid_inst = (valid & 0b10) >> 1;
        info->temp_inst = microkit_mr_get(SDDF_TMU_GET_TEMP_INST);
        info->temp_avg = microkit_mr_get(SDDF_TMU_GET_TEMP_AVG);
    }

    return ret;
}

