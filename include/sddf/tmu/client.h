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
 * Enable or disable the TMU via PPC to the passive TMU driver.
 * @param channel of TMU driver.
 * @param enable true to enable, false to disable.
 * @return 0 on success, 1 on failure.
 */
static inline int sddf_tmu_set_enabled(microkit_channel channel, bool enable)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_TMU_SET_ENABLED, 1);
    microkit_mr_set(SDDF_TMU_SET_ENABLED_ENABLE, enable ? 1 : 0);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Set the IRQ forwarding mode via PPC to the passive TMU driver.
 * @param channel of TMU driver.
 * @param mode IRQ mode (disabled, instantaneous, or average).
 * @return 0 on success, 1 on failure.
 */
static inline int sddf_tmu_set_irq_mode(microkit_channel channel, sddf_tmu_irq_modes mode)
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
    microkit_mr_set(SDDF_TMU_SET_IRQ_THRESHOLD_THRESHOLD, threshold);

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
    if (ret == SDDF_TMU_GET_TEMP_SUCCESS) {
        info->valid = microkit_mr_get(SDDF_TMU_GET_TEMP_VALIDITY);
        info->temp_inst = microkit_mr_get(SDDF_TMU_GET_TEMP_INST);
        info->temp_avg = microkit_mr_get(SDDF_TMU_GET_TEMP_AVG);
    }

    return ret;
}

