/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// This driver has a notion of a controlling connection which will receive forwarded IRQs
// and has the capability to set thesholds for forwarded IRQs or enable the device.
// All other clients can only request the current temperature.
// Note: this driver does NOT work on imx8m mini devices!

// TODO: add sdfgen support for device resources and driver config.
// TODO: add connection to clock driver to allow setting TMTMIR based on real clock speed rather
// than a compile-time guess. We cannot support adjusting the polling rate by clients without this.

#include <microkit.h>
#include <os/sddf.h>
#include <sddf/tmu/protocol.h>
#include <sddf/tmu/driver.h>
#include "imx8mq-tmu"

// TODO: add sdfgen support for IRQ forward channel and critical temp
#define IRQ_FORWARD_CHANNEL (0)
#define IRQ_INST_CHANNEL (1)
#define IRQ_AVG_CHANNEL (2)
#define IRQ_CRITICAL_CHANNEL (3)
#define CRITICAL_TEMP ((sddf_temp_celsius_t )85) // Warnings will be printed if this is exceeded

sddf_tmu_irq_modes_t current_irq_mode = SDDF_TMU_IRQ_MODE_DISABLED;

void init(void) {
    // Set critical temp
    uint64_t critical_temp_quantised = 0;
    sddf_tmu_err_t ret = degrees_to_quantised(CRITICAL_TEMP, SENSOR_MIN_TEMP, SENSOR_MAX_TEMP,
                                              SENSOR_QUANTISATION, &critical_temp_quantised);
    assert(!ret);
}

void notified(microkit_channel ch)
{
    if (ch == IRQ_FORWARD_CHANNEL) {
        LOG_TMU_DRIVER_ERR("IRQ forward channel should not notify driver!");
    } else if (ch == IRQ_INST_CHANNEL) {
        LOG_TMU_DRIVER("Instantaneous value threshold reached!\n");
        if (current_irq_mode != SDDF_TMU_IRQ_MODE_INSTANTANEOUS) {
            LOG_TMU_DRIVER_ERR("Received spurious instantaneous threshold IRQ!\n");
        }
    } else if (ch == IRQ_AVG_CHANNEL) {
        LOG_TMU_DRIVER("Average value threshold reached!\n");
        if (current_irq_mode != SDDF_TMU_IRQ_MODE_AVG) {
            LOG_TMU_DRIVER_ERR("Received spurious average threshold IRQ!\n");
        }
    } else if (ch == IRQ_CRITICAL_CHANNEL) {
        LOG_TMU_DRIVER_ERR("WARNING: critical temperature of %f exceeded! System may be damaged!\n",
                            CRITICAL_TEMP);
        // clear IRQ state
    } else {
        LOG_TMU_DRIVER_ERR("Unknown channel 0x%x!\n", ch);
    }
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    sddf_pmic_err_t err = 0;
    uint64_t ret_num = 0;
    uint32_t argc = microkit_msginfo_get_count(msginfo);
    switch (microkit_msginfo_get_label(msginfo)) {
        case SDDF_TMU_SET_ENABLED:
            if (ch != IRQ_FORWARD_CHANNEL) {
                LOG_PMU_DRIVER_ERR("Client %u is not permitted to TMU_SET_ENABLED!\n", ch);
                err = SDDF_TMU_ERR_UNPERMITTED;
                break;
            }
        case SDDF_TMU_SET_IRQ_MODE:
            if (ch != IRQ_FORWARD_CHANNEL) {
                LOG_PMU_DRIVER_ERR("Client %u is not permitted to TMU_SET_IRQ_MODE!\n", ch);
                err = SDDF_TMU_ERR_UNPERMITTED;
                break;
            }
        case SDDF_TMU_SET_IRQ_THESHOLD:
            if (ch != IRQ_FORWARD_CHANNEL) {
                LOG_PMU_DRIVER_ERR("Client %u is not permitted to TMU_SET_IRQ_THRESHOLD!\n", ch);
                err = SDDF_TMU_ERR_UNPERMITTED;
                break;
            }
        case SDDF_TMU_SET_GET_TEMP:

    default:
        LOG_TMU_DRIVER_ERR("Unknown request %lu to TMU driver from channel %u\n",
                       microkit_msginfo_get_label(msginfo), ch);
        err = SDDF_TMU_ERR_BAD_PPC_CALL;
    }

    return microkit_msginfo_new(err, ret_num);
}
