/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <stdint.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/timer_common.h>
#include <sddf/util/util.h>
#include <sddf/util/arch_timestamp_counter.h>

/**
 * Request a timeout via PPC into the passive timer driver.
 * Use the label to indicate this request.
 * @param channel ID of the timer driver.
 * @param timeout relative timeout in nanoseconds.
 */
static inline void sddf_timer_set_timeout(unsigned int channel, uint64_t timeout)
{
    sddf_set_mr(0, timeout);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_TIMER_SET_TIMEOUT, 0, 0, 1));
}

/**
 * Request the time since start up.
 * @return the time in nanoseconds since start up.
 */
static inline uint64_t sddf_timer_time_now(void)
{
    return ticks_to_ns(sddf_read_counter(), sddf_read_freq());
}
