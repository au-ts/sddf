/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <stdint.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/timer/timer_common.h>
#include <sddf/util/util.h>
#include <sddf/util/arch_timestamp_counter.h>

/**
 * Request a timeout via the timer virt.
 * @param reference to timer client configuration
 * @param timeout relative timeout in nanoseconds.
 */
static inline void sddf_timer_set_timeout(const timer_client_config_t *config, uint64_t timeout)
{
    uint64_t ticks = ns_to_ticks(timeout, sddf_read_freq());
    uint64_t now = sddf_read_counter();
    timeout = now + ticks;
    uint64_t *slot = (uint64_t *)config->req_vaddr;
    __atomic_store_n(slot, timeout, __ATOMIC_RELEASE);
    sddf_notify(config->virt_id);
}

/**
 * Request the time since start up.
 * @return the time in nanoseconds since start up.
 */
static inline uint64_t sddf_timer_time_now(void)
{
    return ticks_to_ns(sddf_read_counter(), sddf_read_freq());
}
