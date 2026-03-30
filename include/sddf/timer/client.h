/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <stdint.h>
#include <sddf/timer/protocol.h>

/**
 * Request a timeout via PPC into the passive timer virt.
 * @param channel ID of the timer virt.
 * @param timeout absolute timestamp in nanoseconds.
 * @param period period of this timeout for repeats. set to 0 for no period.
 * @param *id, returned ID of timeout, used for cancelling it.
 * @return zero on success
 */
static inline int sddf_timer_set_timeout(unsigned int channel, uint64_t timestamp,
                                         uint64_t period, uint64_t *id)
{
    microkit_mr_set(SDDF_TIMER_REQ_TIMEOUT_TIMEOUT, timestamp);
    microkit_mr_set(SDDF_TIMER_REQ_TIMEOUT_PERIOD, period);
    microkit_msginfo msginfo = sddf_ppcall(channel, microkit_msginfo_new(
        SDDF_TIMER_REQ_TIMEOUT, 2));
    // handle response
    if (microkit_msginfo_get_label(msginfo) == SDDF_TIMER_ERR_OK) {
        uint64_t returned_id = microkit_mr_get(SDDF_TIMER_REQ_TIMEOUT_RET_ID);
        *id = returned_id;
        return 0;
    }
    // Return error code from label
    return (microkit_msginfo_get_label(msginfo));
}

/**
 * Request the time since start up via PPC into the passive timer virt.
 * @param channel ID of the timer virt.
 * @return the time in nanoseconds since start up.
 */
static inline uint64_t sddf_timer_time_now(unsigned int channel)
{
    sddf_ppcall(channel, microkit_msginfo_new(SDDF_TIMER_GET_TIME, 0));
    return microkit_mr_get(0);
}

/**
 * Request a timeout relative to the current time via PPC into the passive timer virt.
 */
static inline int sddf_timer_set_relative_timeout(unsigned int channel, uint64_t delay,
                                         uint64_t *id)
{
    uint64_t now = sddf_timer_time_now(channel);
    return sddf_timer_set_timeout(channel, now + delay, 0, id);
}

/**
 * Cancel an existing timeout.
 * @param channel ID of the timer virt.
 * @param timeout_id ID of timeout to cancel.
 * @return 0 on success, otherwise error
 */
static inline int sddf_timer_cancel_timeout(unsigned int channel, uint64_t timeout_id)
{
    microkit_mr_set(SDDF_TIMER_CANCEL_TIMEOUT_ID, timeout_id);
    microkit_msginfo msginfo = sddf_ppcall(channel, microkit_msginfo_new(
        SDDF_TIMER_CANCEL_TIMEOUT, 1));
    return (microkit_msginfo_get_label(msginfo) != SDDF_TIMER_ERR_OK);
}
