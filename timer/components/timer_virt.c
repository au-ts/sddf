/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/timer_virt.h>
#include <sddf/util/util.h>

__attribute__((__section__(".timer_virt_config"))) timer_virt_config_t config;

// Priority heap for managing timeouts
static timer_heap_t timeouts;


void notified(microkit_channel ch)
{

}

static inline uint64_t get_time_ns(void)
{
    // Get from driver
    // TODO: replace with absolute timestamping from time page
    LOG_TIMER_VIRT("getting time\n");
    return timer_virt_get_time();
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    LOG_TIMER_VIRT("ppc from channel %u\n", ch);
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        seL4_SetMR(0, time_ns);
        return microkit_msginfo_new(0, 1);
    }
    case SDDF_TIMER_REQ_TIMEOUT: {
        uint64_t curr_time = get_time_ns();
        uint64_t offset_ns = seL4_GetMR(0);
        LOG_TIMER_VIRT("setting timeout for %zu\n", offset_ns);
        timer_heap_insert(&timeouts, curr_time + offset_ns, ch);
        process_timeouts();
        break;
    }
    default:
        LOG_TIMER_VIRT("Unknown request %lu to timer from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        break;
    }

    return microkit_msginfo_new(0, 0);
}


void init(void)
{
    // Initialise priority heap
    timer_heap_init(&timeouts);
}
