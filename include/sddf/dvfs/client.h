/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stddef.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/dvfs/protocol.h>

#ifdef CONFIG_PLAT_ZYNQMP_ZCU102

const size_t OPP_TABLE_LEN = 4;
const size_t CPU_INFO_LEN = 4;
#endif

#define SDDF_DVFS_GET_POINT 0
#define SDDF_DVFS_SET_POINT 1

#define SDDF_DVFS_SUCCESS 0
#define SDDF_DVFS_RESPONSE_ERROR 1

/**
 * Get the OPP of a specific CPU core via PPC into the DVFS driver.
 * Use the label to indicate this request.
 * A return value of zero means the request is completed successfully.
 * @param channel ID of the DVFS driver.
 * @param core_ident The unique identifier of the CPU core.
 * @param freq A pointer to a unsighed integer to pass back the returned frequency.
 */
static inline int32_t sddf_dvfs_get_point(unsigned int channel, uint64_t core_ident, op_point_idx_t *point)
{
    sddf_set_mr(0, core_ident);

    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_DVFS_GET_POINT, 0, 0, 1));

    uint32_t error = sddf_get_mr(0);
    if (error == SDDF_DVFS_SUCCESS) {
        *point = (op_point_idx_t) sddf_get_mr(1);
    }
    return error;
}

/**
 * Set the OPP of a specific CPU core via PPC into the DVFS driver.
 * Use the label to indicate this request.
 * A return value of zero means the request is completed successfully.
 * @param channel ID of the DVFS driver.
 * @param core_ident The unique identifier of the CPU core.
 * @param freq The desired core frequency.
 */
static inline int32_t sddf_dvfs_set_point(unsigned int channel, uint64_t core_ident, op_point_idx_t point)
{
    sddf_set_mr(0, core_ident);
    sddf_set_mr(1, point);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_DVFS_SET_POINT, 0, 0, 2));

    return sddf_get_mr(0);
}
