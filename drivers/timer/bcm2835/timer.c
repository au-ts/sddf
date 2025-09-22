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

//#if !defined(CONFIG_PLAT_bcm2835)
//#error "Driver assumes 1MHz clock frequency, check if your platform supports that"
//#endif

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

typedef struct {
    /* Registers
     * bcm2835 System Timer peripheral provides four 32-bit timer channels
     * and one 64-bit free running counter. */
    uint32_t cs;    /* 0x00: system timer control/status */
    uint32_t clo;   /* 0x04: system timer counter lower 32 bits */
    uint32_t chi;   /* 0x08: system timer counter higher 32 bits */
    uint32_t c0;    /* 0x0c: system timer compare 0 */
    uint32_t c1;    /* 0x10: system timer compare 1 */
    uint32_t c2;    /* 0x14: system timer compare 2 */
    uint32_t c3;    /* 0x18: system timer compare 3 */
} bcm2835_timer_regs_t;

static volatile bcm2835_timer_regs_t *timer_regs;

#define MAX_TIMEOUTS 6
static uint64_t timeouts[MAX_TIMEOUTS];

static inline uint64_t get_ticks_in_ns(void)
{
    uint64_t value_h = (uint64_t)timer_regs->chi;
    uint64_t value_l = (uint64_t)timer_regs->clo;
    uint64_t value_ticks = (value_h << 32) | value_l;

    /* convert from ticks to nanoseconds */
    uint64_t value_whole_seconds = value_ticks / 1000000;
    uint64_t value_subsecond_ticks = value_ticks % 1000000;
    uint64_t value_subsecond_ns = (value_subsecond_ticks * NS_IN_S) / 1000000;
    uint64_t value_ns = value_whole_seconds * NS_IN_S + value_subsecond_ns;

    return value_ns;
}

void set_timeout(uint64_t ns)
{
    timer_regs->c0 = ns / 1000;
}

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            microkit_notify(1 + i);
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
        uint64_t ns = next_timeout - curr_time;
        set_timeout(ns);
    }
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    /* Ack any IRQs that were delivered before the driver started. */
    microkit_irq_ack(device_resources.irqs[0].id);

    timer_regs = (bcm2835_timer_regs_t *)device_resources.regions[0].region.vaddr;

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }
}

void notified(microkit_channel ch)
{
    //chirag: for now assuming we only use one timer which is c0...
    assert(ch == device_resources.irqs[0].id);

    /* Handled irq -> clear device interrupt */
    uint64_t curr_time = get_ticks_in_ns();
    process_timeouts(curr_time);
    timer_regs->cs = (1 << 0);
    microkit_deferred_irq_ack(ch);
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
        timeouts[ch - 1] = curr_time + offset_us;
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