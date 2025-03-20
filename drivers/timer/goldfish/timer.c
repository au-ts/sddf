/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/util/udivmodti4.h>
#include <sddf/resources/device.h>

#define MAX_TIMEOUTS 6

/* taken from: https://github.com/torvalds/linux/blob/master/include/clocksource/timer-goldfish.h */
typedef struct {
    /* Registers */
    uint32_t time_low;            /* 0x00: get low bits of current time and update time_high */
    uint32_t time_high;           /* 0x04: get high bits of time at last time_low read */
    uint32_t alarm_low;           /* 0x08: set low bits of alarm and activate it */
    uint32_t alarm_high;          /* 0x0c: set high bits of next alarm */
    uint32_t irq_enabled;         /* 0x10: set to 1 to enable alarm interrupt */
    uint32_t clear_alarm;         /* 0x14: set to 1 to disarm an existing alarm */
    uint32_t alarm_status;        /* 0x18: alarm status (1 running; 0 not) */
    uint32_t clear_interrupt;     /* 0x1c: set to 1 to clear interrupt */
} goldfish_timer_regs_t;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
static volatile goldfish_timer_regs_t *timer_regs;

static inline uint64_t get_ticks_in_ns(void)
{
    uint64_t time = (uint64_t)timer_regs->time_low;
    time |= ((uint64_t)timer_regs->time_high) << 32;
    return time;
}

void set_timeout(uint64_t timeout)
{
    timer_regs->alarm_high = (uint32_t)(timeout >> 32);
    timer_regs->alarm_low = (uint32_t)timeout;
    timer_regs->irq_enabled = 1U;
}

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
    timer_regs = (goldfish_timer_regs_t *)device_resources.regions[0].region.vaddr;

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }
}

void notified(microkit_channel ch)
{
    assert(ch == device_resources.irqs[0].id);
    microkit_deferred_irq_ack(ch);

    /* Handled irq -> clear device interrupt */
    timer_regs->clear_interrupt = 1;
    uint64_t curr_time = get_ticks_in_ns();
    process_timeouts(curr_time);
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
        sddf_dprintf("TIMER DRIVER|LOG: Unknown request %lu to timer from channel %u\n",
                     microkit_msginfo_get_label(msginfo), ch);
        break;
    }

    return microkit_msginfo_new(0, 0);
}
