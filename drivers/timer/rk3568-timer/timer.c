/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;


/* offset for the 2 interrupt channels */
#define CLIENT_CH_START 2
#define MAX_TIMEOUTS 6
//static uint64_t timeouts[MAX_TIMEOUTS];
sddf_channel counter_irq;

static inline uint64_t get_ticks_in_ns(void)
{
    return 0;
}

void set_timeout(uint64_t ns)
{
    return;
}

static void process_timeouts(uint64_t curr_time)
{
    return;
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    sddf_dprintf("Touch mem region phys 0x%lx vaddr: %p\n", device_resources.regions[0].io_addr, (uint64_t*)device_resources.regions[0].region.vaddr);
    sddf_dprintf("0x%lx\n", *((uint64_t*)device_resources.regions[0].region.vaddr));

    // TODO: init device, check irqs r working. Maybe use one timer for a timestamp (always running, read value in get_ticks_in_ns()), and one timer for timeouts (on IRQs process_timeouts, keep queue of IRQs)
    counter_irq = device_resources.irqs[0].id;
}

void notified(sddf_channel ch)
{
    if (ch == counter_irq) {
        sddf_dprintf("TIMER DRIVER|LOG: notified on counter_irq channel\n");
    } else {
        sddf_dprintf("TIMER DRIVER|LOG: unexpected notification from channel %u\n", ch);
    }
    sddf_deferred_irq_ack(ch);
}

seL4_MessageInfo_t protected(sddf_channel ch, seL4_MessageInfo_t msginfo)
{
    switch (seL4_MessageInfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        uint64_t time_ns = 0; //XXX
        sddf_set_mr(0, time_ns);
        return seL4_MessageInfo_new(0, 0, 0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        //uint64_t curr_time = get_ticks_in_ns();
        //uint64_t offset_us = (uint64_t)(sddf_get_mr(0));
        //timeouts[ch - CLIENT_CH_START] = curr_time + offset_us;
        //process_timeouts(curr_time);
        break;
    }
    default:
        sddf_dprintf("TIMER DRIVER|LOG: Unknown request %lu to timer from channel %u\n",
                     seL4_MessageInfo_get_label(msginfo), ch);
        break;
    }

    return seL4_MessageInfo_new(0, 0, 0, 0);
}
