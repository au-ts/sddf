/*
 * Copyright 2024, UNSW
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

volatile void *regs;
#define REG_PTR(off)     ((volatile uint32_t *)((regs) + (off)))

#define REG_COUNTER_CTL 0x0C
#define REG_COUNTER_VALUE 0x18
#define REG_COUNTER_CLK_CTL 0x0
#define REG_COUNTER_INTERVAL_COUNT 0x24
#define REG_COUNTER_MATCH1 0x3C
#define REG_COUNTER_MATCH2 0x48
#define REG_COUNTER_IER 0x60
#define REG_COUNTER_ISR 0x54

static inline uint64_t get_ticks_in_ns(void)
{
    return 0;
}

void set_timeout(uint64_t timeout)
{
}

#define MAX_TIMEOUTS 6
static uint64_t timeouts[MAX_TIMEOUTS];

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            microkit_notify(i);
            timeouts[i] = UINT64_MAX;
        }
    }

    uint64_t next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] < next_timeout) {
            next_timeout = timeouts[i];
        }
    }

    if (next_timeout != UINT64_MAX) {
        set_timeout(next_timeout);
    }
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    regs = device_resources.regions[0].region.vaddr;

    uint32_t ctrl = *REG_PTR(REG_COUNTER_CTL);
    if (ctrl & 0x1) {
        sddf_dprintf("timer counter is not started\n");
    } else {
        sddf_dprintf("timer counter is started\n");
    }

    // Table 14-9
    // stop timer
    *REG_PTR(REG_COUNTER_CTL) = ctrl | BIT(0);
    // Reset counter control reg
    *REG_PTR(REG_COUNTER_CTL) = 0x21;
    *REG_PTR(REG_COUNTER_CLK_CTL) = 0x0;
    *REG_PTR(REG_COUNTER_INTERVAL_COUNT) = 0x0;
    *REG_PTR(REG_COUNTER_MATCH1) = 0x0;
    *REG_PTR(REG_COUNTER_MATCH2) = 0x0;
    *REG_PTR(REG_COUNTER_IER) = 0x0;
    *REG_PTR(REG_COUNTER_ISR) = 0x0;
    // Reset counter
    *REG_PTR(REG_COUNTER_CTL) = ctrl | (1 << 4);
    // Set up interval value
    *REG_PTR(REG_COUNTER_IER) = 0x1;
    // clock 100MHz ? below will tick every second
    *REG_PTR(REG_COUNTER_INTERVAL_COUNT) = 0x5F5E100;
    ctrl = ctrl | BIT(1);
    // Enable interval mode
    *REG_PTR(REG_COUNTER_CTL) = ctrl;
    //Start the counter
    *REG_PTR(REG_COUNTER_CTL) = ctrl ^ 0x1;
    sddf_dprintf("start counter: 0x%x\n", ctrl ^ 0x1);
    sddf_dprintf("REG_COUNTER_CTL is: 0x%x\n", *REG_PTR(REG_COUNTER_CTL));

    //for (int i = 0; i < 100; i++) {
    sddf_dprintf("value: %d\n", *REG_PTR(REG_COUNTER_VALUE));
    //}
}

void notified(microkit_channel ch)
{
    assert(ch == device_resources.irqs[0].id);
    microkit_deferred_irq_ack(ch);
    sddf_dprintf("Interrupt received!\n");
    sddf_dprintf("Interrupt reg: 0x%x\n", *REG_PTR(REG_COUNTER_ISR));
    sddf_dprintf("Interrupt reg: 0x%x\n", *REG_PTR(REG_COUNTER_ISR));
    sddf_dprintf("counter val: 0x%x\n", *REG_PTR(REG_COUNTER_VALUE));
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        uint64_t time_ns = get_ticks_in_ns();
        seL4_SetMR(0, time_ns);
        return microkit_msginfo_new(0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = get_ticks_in_ns();
        uint64_t offset_us = (uint64_t)(seL4_GetMR(0));
        timeouts[ch] = curr_time + offset_us;
        process_timeouts(curr_time);
        break;
    }
    default:
        sddf_dprintf("TIMER DRIVER|LOG: Unknown request %lu to timer from channel %u\n", microkit_msginfo_get_label(msginfo),
                     ch);
        break;
    }

    return microkit_msginfo_new(0, 0);
}
