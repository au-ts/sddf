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
#include "imx8mq-tmu.h"

// TODO: add sdfgen support for IRQ forward channel and critical temp
#define IRQ_CHANNEL (0)
#define IRQ_FORWARD_CHANNEL (1)
#define CRITICAL_TEMP ((sddf_temp_celsius_t )85) // Warnings will be printed if this is exceeded

// TODO: sdfgen support for passing in this resource
#define TMU_REG_BASE (0x30260000)
volatile imx8mq_tmu_regs_t *regs;

sddf_tmu_irq_modes_t current_irq_mode = SDDF_TMU_IRQ_MODE_DISABLED;
sddf_temp_celsius_t current_irq_thresh = SENSOR_MAX_TEMP;

static inline void enable_tmu(void) {
    // disable monitoring to reconfigure
    regs->tmr &= ~TMU_TMR_ME_BIT;
    // clear irqs
    regs->tidr |= (TMU_TIDR_ITTE_BIT | TMU_TIDR_ATTE_BIT | TMU_TIDR_ATCTE_BIT);

    #ifdef SDDF_PMU_ENABLE_IRQ
    // clear interrupt site capture register
    regs->tiscr &= ~(TMU_TISCR_ASITE_MASK << TMU_TISCR_ASITE_OFFSET);
    regs->tiscr &= ~(TMU_TISCR_ISITE_MASK << TMU_TISCR_ISITE_OFFSET);

    // clear critical interrupt site capture register
    regs->ticscr &= ~(TMU_TICSCR_CASITE_MASK << TMU_TICSCR_CASITE_OFFSET);

    // enable critical irq and suitable IRQ mode bits
    regs->tier |= TMU_TIER_ATCTEIE_BIT;
    if (current_irq_mode == SDDF_TMU_IRQ_MODE_INSTANTANEOUS) {
        regs->tier |= TMU_TIER_ITTEIE_BIT;
    } else if (current_irq_mode == SDDF_TMU_IRQ_MODE_AVG) {
        regs->tier |= TMU_TIER_ATTEIE_BIT;
    }

    // Set critical temp. We don't use this for the protocol, but it is a handy utility
    // to print errors if the board is in the process of melting down.
    // enable theshold monitoring + program critical temperature theshold
    regs->tmhtactr |= ((TMU_TMHTACTR_EN_BIT) | (CRITICAL_TEMP & TMU_TMHTACTR_TEMP_MASK));

    // repeat for IRQ mode threshold (must happen after enabling IRQ)
    if (current_irq_mode == SDDF_TMU_IRQ_MODE_INSTANTANEOUS) {
        regs->tmhtitr |= (TMU_TMHTITR_EN_BIT | ((uint64_t)current_irq_thresh & TMU_TMHTITR_TEMP_MASK));
    } else if (current_irq_mode == SDDF_TMU_IRQ_MODE_AVG) {
        regs->tmhtatr |= (TMU_TMHTATR_EN_BIT | ((uint64_t)current_irq_thresh & TMU_TMHTATR_TEMP_MASK));
    }
    #endif
    // set low pass filter for average to 4 samples
    regs->tmr |= (0b10 & TMU_TMR_ALPF_MASK) << TMU_TMR_ALPF_OFFSET;
    // set a conservative polling rate that should be adequate for all input clock
    // speeds. rate is 0.08 to 0.2 seconds depending on input clock.
    regs->tmtmir |= (0b0011 & TMU_TMTMIR_TMI_MASK);

    // enable whole monitor and enable CPU monitoring site
    regs->tmr |= (TMU_TMR_ME_BIT | TMU_TMR_MSITE_ARM_BIT);
}

static inline void get_temp(sddf_tmu_temp_info_t *info) {
    info->valid_inst = (regs->tritsr0 & TMU_TRITSR_V_BIT) != 0;
    info->valid_avg = (regs->tratsr0 & TMU_TRATSR_V_BIT) != 0;
    uint64_t inst = regs->tritsr0 & TMU_TRITSR_TEMP_MASK;
    uint64_t avg = regs->tratsr0 & TMU_TRATSR_TEMP_MASK;
    info->temp_inst = (sddf_temp_celsius_t) inst;
    info->temp_avg = (sddf_temp_celsius_t) avg;
    if (!info->valid_inst) {
        LOG_TMU_DRIVER_ERR("Invalid instantaneous reading detected\n");
    }
    if (!info->valid_avg) {
        LOG_TMU_DRIVER_ERR("Invalid average reading detected\n");
    }
}

void init(void) {
    // TODO: replace with device resource
    regs = (volatile imx8mq_tmu_regs_t *)TMU_REG_BASE;
    enable_tmu();
}

void notified(microkit_channel ch)
{

    // Sanity: make sure we are still monitoring. If the monitoring interval is exceeded,
    // the device will stop silently.
    if (regs->tsr & TMU_TSR_MIE_BIT) {
        LOG_TMU_DRIVER_ERR("Monitoring has failed due to polling timing out!\n");
        assert(false);  // If you get this, increase the interval setting in init()
    }

    if (ch == IRQ_FORWARD_CHANNEL) {
        LOG_TMU_DRIVER_ERR("IRQ forward channel should not notify driver!");
        return;
    } else if (ch == IRQ_CHANNEL) {
        // check IRQ source
        if (regs->tidr & TMU_TIDR_ITTE_BIT) {
            LOG_TMU_DRIVER("Instantaneous value threshold reached!\n");
            if (current_irq_mode != SDDF_TMU_IRQ_MODE_INSTANTANEOUS) {
                LOG_TMU_DRIVER_ERR("Received spurious instantaneous threshold IRQ!\n");
            }
            microkit_notify(IRQ_FORWARD_CHANNEL);
        }
        if (regs->tidr & TMU_TIDR_ATTE_BIT) {
            LOG_TMU_DRIVER("Average value threshold reached!\n");
            if (current_irq_mode != SDDF_TMU_IRQ_MODE_AVG) {
                LOG_TMU_DRIVER_ERR("Received spurious average threshold IRQ!\n");
            }
            microkit_notify(IRQ_FORWARD_CHANNEL);
        }
        if (regs->tidr & TMU_TIDR_ATCTE_BIT) {
            LOG_TMU_DRIVER_ERR("WARNING: critical temperature of %f exceeded! System may be damaged!\n",
                                CRITICAL_TEMP);
            }
    } else {
        LOG_TMU_DRIVER_ERR("Unknown channel 0x%x!\n", ch);
    }
    // Check if temperature exceeded range
    bool invalid_low = regs->tsr & TMU_TSR_ORL_BIT;
    bool invalid_high = regs->tsr & TMU_TSR_ORH_BIT;
    if (invalid_low) {
        LOG_TMU_DRIVER_ERR("Avg monitoring detected temperature <= %f (out of range)!\n",
                           SENSOR_MIN_TEMP);
    }
    if (invalid_high) {
        LOG_TMU_DRIVER_ERR("Avg monitoring detected temperature >= %f (out of range)!\n",
                           SENSOR_MIN_TEMP);
    }
    if (invalid_high && invalid_low) {
        LOG_TMU_DRIVER_ERR("Temperatures are out of high and low range! Something is wrong!\n");
    }
    microkit_irq_ack(ch);

    // Re-enable the device to clear all IRQ flags.
    // There are lots of conditions that cause the device to stop, requiring multiple bits.
    // It's easier to simply reset than to handle all of these!
    enable_tmu();
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    // Sanity: make sure we are still monitoring. If the monitoring interval is exceeded,
    // the device will stop silently.
    if (regs->tsr & TMU_TSR_MIE_BIT) {
        LOG_TMU_DRIVER_ERR("Monitoring has failed due to polling timing out!\n");
        assert(false);  // If you get this, increase the interval setting in init()
    }
    sddf_tmu_err_t err = SDDF_TMU_ERR_OK;
    uint64_t ret_num = 1;
    sddf_tmu_temp_info_t temp;
    switch (microkit_msginfo_get_label(msginfo)) {
        case SDDF_TMU_SET_IRQ_MODE:
            if (ch != IRQ_FORWARD_CHANNEL) {
                LOG_TMU_DRIVER_ERR("Client %u is not permitted to TMU_SET_IRQ_MODE!\n", ch);
                err = SDDF_TMU_ERR_UNPERMITTED;
                break;
            }
            sddf_tmu_irq_modes_t new_mode = (sddf_tmu_irq_modes_t)
                microkit_mr_get(SDDF_TMU_SET_IRQ_MODE_MODE);

            if (new_mode >= SDDF_TMU_IRQ_MODES_NUM) {
                LOG_TMU_DRIVER_ERR("Invalid IRQ mode %d supplied!\n", new_mode);
                err = SDDF_TMU_ERR_EINVAL;
            } else {
                current_irq_mode = new_mode;
                enable_tmu();
            }
            break;

        case SDDF_TMU_SET_IRQ_THRESHOLD:
            if (ch != IRQ_FORWARD_CHANNEL) {
                LOG_TMU_DRIVER_ERR("Client %u is not permitted to TMU_SET_IRQ_THRESHOLD!\n", ch);
                err = SDDF_TMU_ERR_UNPERMITTED;
                break;
            }
            sddf_temp_celsius_t new_temp = (sddf_temp_celsius_t) microkit_mr_get(SDDF_TMU_SET_IRQ_THESHOLD_THESH);
            // Check theshold is valid
            if (new_temp > SENSOR_MAX_TEMP || new_temp < SENSOR_MIN_TEMP) {
                LOG_TMU_DRIVER_ERR("Invalid temperature %f, must be in range [%f, %f]\n",
                                   new_temp, SENSOR_MIN_TEMP, SENSOR_MAX_TEMP);
                err = SDDF_TMU_ERR_EINVAL;
            } else {
                current_irq_thresh = new_temp;
                LOG_TMU_DRIVER("IRQ thesh set to %f\n", new_temp);
                enable_tmu();
            }
            break;
        case SDDF_TMU_GET_TEMP:
            get_temp(&temp);
            microkit_mr_set(SDDF_TMU_GET_TEMP_VALIDITY, (temp.valid_inst | (temp.valid_avg << 1)));
            microkit_mr_set(SDDF_TMU_GET_TEMP_INST, temp.temp_inst);
            microkit_mr_set(SDDF_TMU_GET_TEMP_AVG, temp.temp_avg);
            ret_num = 3;
            break;

    default:
        LOG_TMU_DRIVER_ERR("Unknown request %lu to TMU driver from channel %u\n",
                       microkit_msginfo_get_label(msginfo), ch);
        err = SDDF_TMU_ERR_BAD_PPC_CALL;
    }

    return microkit_msginfo_new(err, ret_num);
}
