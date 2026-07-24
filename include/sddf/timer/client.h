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
 * If architecture counter is usable, fast-paths reading the hardware counter
 * locally via sddf_read_counter().
 * If unusable, silently falls back to a PPC into the passive timer driver.
 * @param channel ID of the timer driver.
 * @return the time in nanoseconds since start up.
 */
static inline uint64_t sddf_timer_time_now(unsigned int channel)
{
    // TODO: remove this guard once remaining architectures supported
#if defined(CONFIG_ARCH_X86)
    uint64_t freq = sddf_read_freq();
    if (likely(freq != 0)) {
        return ticks_to_ns(sddf_read_counter(), freq);
    }
#endif // CONFIG_ARCH_X86

    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_TIMER_GET_TIME, 0, 0, 0));
    return sddf_get_mr(0);
}
