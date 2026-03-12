/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Note: the DVFS driver only implements the operating point table and a protocol
//       for shifting between points. Thermal control is implemented by a client.
//
//       This platform has a global clock and regulator, so the CPU/reg field has no
//       impact on settings and the returned operating point is shared for all CPUs.
//       We may want to encode the notion of dependent operating points in the protocol
//       in the future as this disambiguates things.

#include <stdbool.h>
#include <os/sddf.h>
#include <sddf/dvfs/dvfs_driver.h>
#include <sddf/resources/device.h>
#include <sddf/util/util.h>
#include <sddf/clk/client.h>
#include <sddf/clk/imx8mq-bindings.h>
#include <sddf/pmic/bd71837amwv-bindings.h>
#include <sddf/pmic/client.h>
#include <sddf/pmic/protocol.h>
#include <sddf/dvfs/protocol.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

// TODO: replace with sdfgen resources
#define CLK_DRIVER_CHANNEL ((uint64_t) 0)
#define PMIC_DRIVER_CHANNEL (1)

// TODO: support passing in operating point table from sdfgen
#define OP_TABLE_SZ 4
const dvfs_op_point_t imx_op_point_table[OP_TABLE_SZ] = {
    { .freq_hz = 0x2faf0800ULL, .voltage_uv = 0xdbba0ULL, .latency_ns = 0xEE6C },
    { .freq_hz = 0x3b9aca00ULL, .voltage_uv = 0xdbba0ULL, .latency_ns = 0xEE6C },
    { .freq_hz = 0x4d7c6d00ULL, .voltage_uv = 0xf4240ULL, .latency_ns = 0xEE6C },
    { .freq_hz = 0x59682f00ULL, .voltage_uv = 0xf4240ULL, .latency_ns = 0xEE6C }
};

#define IMX_NUM_CORES 4
const dvfs_core_info_t core_list[IMX_NUM_CORES] = {
    { .core_id = 0, .clk_src_id = IMX8MQ_CLK_ARM, .regulator_id = BD718XX_BUCK2,
        .op_point_tbl = imx_op_point_table },
    { .core_id = 1, .clk_src_id = IMX8MQ_CLK_ARM, .regulator_id = BD718XX_BUCK2,
        .op_point_tbl = imx_op_point_table },
    { .core_id = 2, .clk_src_id = IMX8MQ_CLK_ARM, .regulator_id = BD718XX_BUCK2,
        .op_point_tbl = imx_op_point_table },
    { .core_id = 3, .clk_src_id = IMX8MQ_CLK_ARM, .regulator_id = BD718XX_BUCK2,
        .op_point_tbl = imx_op_point_table }
};

// Cluster shares a single clock and power source, just one index.
op_point_idx_t curr_op_point = 0;

static inline bool core_id_valid(uint64_t core_id) {
    if (core_id > IMX_NUM_CORES -1) {
        return false;
    }
    return true;
}


static inline bool op_point_idx_valid(op_point_idx_t point) {
    if (point > OP_TABLE_SZ -1) {
        return false;
    }
    return true;
}

static inline int do_set_frequency(op_point_idx_t op_point_idx) {
    // Homogeneous cores with shared clock. Use core 0 for reference always.
    uint64_t target_freq = imx_op_point_table[op_point_idx].freq_hz;
    uint64_t set_ret_rate = 0;
    int ret = sddf_clk_set_rate(CLK_DRIVER_CHANNEL, core_list[0].clk_src_id,
                                target_freq, &set_ret_rate);
    if (ret) {
        LOG_DVFS_DRIVER_ERR("Failed to set clock rate!\n");
        return ret;
    }
    // assert(target_freq == set_ret_rate);

    uint64_t returned_freq = 0;
    ret = sddf_clk_get_rate(CLK_DRIVER_CHANNEL, core_list[0].clk_src_id,
                                &returned_freq);
    if (ret) {
        LOG_DVFS_DRIVER_ERR("Failed to measure clock for confirmation!\n");
        return ret;
    }
    if (returned_freq != target_freq) {
        LOG_DVFS_DRIVER_ERR("Target freq %zu != actual freq %zu!\n",
                            target_freq, returned_freq);
        return 1;
    } else {
        LOG_DVFS_DRIVER("Successfully set freq to %zu (target=%zu)!\n",
                            returned_freq, target_freq);
    }
    return 0;
}

static inline int do_set_voltage(op_point_idx_t op_point_idx) {
    uint64_t target_voltage = imx_op_point_table[op_point_idx].voltage_uv;

    int ret = sddf_pmic_set_vout(PMIC_DRIVER_CHANNEL, core_list[0].regulator_id,
                                 target_voltage);
    if (ret  != SDDF_PMIC_ERR_OK) {
        LOG_DVFS_DRIVER_ERR("Failed to set voltage for operating point %zu @ %zu uV!\n",
                            op_point_idx, target_voltage);
        return -1;
    } else {
        LOG_DVFS_DRIVER("Set voltage for operating point %zu @ %zu uV!\n",
                            op_point_idx, target_voltage);
    }
    return 0;
}

static inline int set_op_point(op_point_idx_t new_point) {
    curr_op_point = new_point;
    int ret0 = do_set_frequency(curr_op_point);
    int ret1 = do_set_voltage(curr_op_point);
    return (ret0 != 0 || ret1 != 0);
}

void init(void) {
    // Start up: we need to initialise our connections to other drivers and
    // load the initial state. We start at the 0th entry, which should be the
    // lowest operating point by default.
    int ret = set_op_point(0);
    if (ret) {
        LOG_DVFS_DRIVER_ERR("Failed to set initial operating point! Halting!\n");
        while (1) {}
    }
    LOG_DVFS_DRIVER("Initialised\n");
}


void notified(microkit_channel ch) {}

microkit_msginfo protected(sddf_channel ch, microkit_msginfo msginfo) {
    uint64_t core_identifier = 0;
    op_point_idx_t new_point = 0;
    switch (microkit_msginfo_get_label(msginfo)) {
        case SDDF_DVFS_GET_POINT:
            LOG_DVFS_DRIVER("GET_POINT\n");
            core_identifier = sddf_get_mr(0);
            if (!core_id_valid(core_identifier)) {
                LOG_DVFS_DRIVER_ERR("Tried to get frequency with invalid core ID!\n");
                microkit_mr_set(0, SDDF_DVFS_RESPONSE_ERROR);
                return microkit_msginfo_new(0, 1);
            }
            microkit_mr_set(1, curr_op_point);
            return microkit_msginfo_new(0, 2);

        case SDDF_DVFS_SET_POINT:
            LOG_DVFS_DRIVER("SET_POINT\n");
            core_identifier = sddf_get_mr(0);
            new_point = sddf_get_mr(1);
            if (!core_id_valid(core_identifier) || !op_point_idx_valid(new_point)) {
                LOG_DVFS_DRIVER_ERR("Tried to get frequency with invalid core ID or OPP!\n");
                microkit_mr_set(0, SDDF_DVFS_RESPONSE_ERROR);
                return microkit_msginfo_new(0, 1);
            }
            int ret = set_op_point(new_point);
            if (ret) {
                LOG_DVFS_DRIVER_ERR("Failed to set operating point!\n");
                microkit_mr_set(0, SDDF_DVFS_RESPONSE_ERROR);
                return microkit_msginfo_new(0, 1);
            } else {
                microkit_mr_set(0, SDDF_DVFS_SUCCESS);
                return microkit_msginfo_new(0, 1);
            }
        default:
            LOG_DVFS_DRIVER_ERR("Invalid channel %zu!\n", microkit_msginfo_get_label(msginfo));
            microkit_mr_set(0, SDDF_DVFS_RESPONSE_ERROR);
            return microkit_msginfo_new(0, 1);
    }
}
