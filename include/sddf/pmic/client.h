/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/pmic/protocol.h>

/**
 * Enable a given regulator via PPC to the passive PMIC driver.
 * @param channel of PMIC driver.
 * @param reg_id identifier of target regulator.
 * @return 0 on success, nonzero on failure.
 */
static inline sddf_pmic_err_t sddf_pmic_enable_reg(microkit_channel channel, uint32_t reg_id)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_PMIC_ENABLE_REG, 1);
    microkit_mr_set(SDDF_PMIC_ENABLE_REG_REG_ID, reg_id);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Disable a given regulator via PPC to the passive PMIC driver.
 * @param channel of PMIC driver.
 * @param reg_id identifier of target regulator.
 * @return 0 on success, nonzero on failure.
 */
static inline sddf_pmic_err_t sddf_pmic_disable_reg(microkit_channel channel, uint32_t reg_id)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_PMIC_DISABLE_REG, 1);
    microkit_mr_set(SDDF_PMIC_DISABLE_REG_REG_ID, reg_id);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Set the voltage output level for a regulator via PPC to the passive PMIC driver.
 * @param channel of PMIC driver.
 * @param reg_id identifier of target regulator.
 * @param voltage_uv target voltage in microvolts.
 * @return 0 on success, 1 if regulator invalid, 2 if voltage setting invalid.
 */
static inline sddf_pmic_err_t sddf_pmic_set_vout(microkit_channel channel, uint32_t reg_id,
                                     uint64_t voltage_uv)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_PMIC_SET_VOUT, 3);
    microkit_mr_set(SDDF_PMIC_SET_VOUT_REG_ID, reg_id);
    microkit_mr_set(SDDF_PMIC_SET_VOUT_VOLTAGE_UV, voltage_uv);
    // microkit_mr_set(SDDF_PMIC_SET_VOUT_OP_MODE_ID, op_mode_id);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Set the current limit for a regulator via PPC to the passive PMIC driver.
 * @param channel of PMIC driver.
 * @param reg_id identifier of target regulator.
 * @param current_ua target current limit in microamps.
 * @return 0 on success, 1 if regulator invalid, 2 if current setting invalid.
 */
static inline sddf_pmic_err_t sddf_pmic_set_climit(microkit_channel channel, uint32_t reg_id,
                                       uint64_t current_ua)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_PMIC_SET_CLIMIT, 3);
    microkit_mr_set(SDDF_PMIC_SET_CLIMIT_REG_ID, reg_id);
    microkit_mr_set(SDDF_PMIC_SET_CLIMIT_CURRENT_UA, current_ua);
    // microkit_mr_set(SDDF_PMIC_SET_CLIMIT_OP_MODE_ID, op_mode_id);

    msginfo = microkit_ppcall(channel, msginfo);

    return (int)microkit_msginfo_get_label(msginfo);
}

/**
 * Get information about a regulator via PPC to the passive PMIC driver.
 * @param channel of PMIC driver.
 * @param reg_id identifier of target regulator.
 * @param info pointer to structure to populate with regulator information.
 * @return 0 on success, 1 if regulator invalid.
 */
static inline sddf_pmic_err_t sddf_pmic_get_reg_info(microkit_channel channel, uint32_t reg_id,
                                         sddf_pmic_reg_info_t *info)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SDDF_PMIC_GET_REG_INFO, 1);
    microkit_mr_set(SDDF_PMIC_GET_REG_INFO_REG_ID, reg_id);

    msginfo = microkit_ppcall(channel, msginfo);

    int ret = (int)microkit_msginfo_get_label(msginfo);
    if (ret == SDDF_PMIC_GET_REG_INFO_SUCCESS) {
        info->enabled = microkit_mr_get(SDDF_PMIC_GET_REG_INFO_ENABLED);
        info->voltage_uv = microkit_mr_get(SDDF_PMIC_GET_REG_INFO_VOLTAGE_UV);
        info->current_ua = microkit_mr_get(SDDF_PMIC_GET_REG_INFO_CURRENT_UA);
        info->min_voltage_uv = microkit_mr_get(SDDF_PMIC_GET_REG_INFO_MIN_VOLTAGE_UV);
        info->max_voltage_uv = microkit_mr_get(SDDF_PMIC_GET_REG_INFO_MAX_VOLTAGE_UV);
        info->min_current_ua = microkit_mr_get(SDDF_PMIC_GET_REG_INFO_MIN_CURRENT_UA);
        info->max_current_ua = microkit_mr_get(SDDF_PMIC_GET_REG_INFO_MAX_CURRENT_UA);
        info->ramprate = microkit_mr_get(SDDF_PMIC_GET_REG_INFO_RAMPRATE);
    }

    return ret;
}

