/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>

#define MAX_TIMEOUTS 6

#define RK3568_TIMER_MAX_TICKS UINT32_MAX
/* 24 MHz frequency. */
#define RK3568_TIMER_TICKS_PER_SECOND 0x16e3600

#define RK3568_TIMER_DISABLE 0x0
#define RK3568_TIMER_ENABLE (1 << 0)
#define RK3568_TIMER_ENABLE_IRQ (1 << 2)

#define RK3568_TIMER_USER_DEFINED (1 << 1)

#define RK3568_TIMER_SIZE 0x20

typedef struct {
    uint32_t load_count0;
    uint32_t load_count1;
    uint32_t current_value0;
    uint32_t current_value1;
    uint32_t control;
    uint32_t _reserved;
    uint32_t intstatus;
} rk3568_timer_regs_t;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

static volatile rk3568_timer_regs_t *counter_regs;
static volatile rk3568_timer_regs_t *timeout_regs;

microkit_channel timeout_irq;
microkit_channel counter_irq;

static uint64_t get_ticks_in_ns(void)
{
    /* the timer value counts down from the load value */
    uint64_t value_l = (uint64_t)(RK3568_TIMER_MAX_TICKS - counter_regs->current_value0);
    uint64_t value_h = (uint64_t)(RK3568_TIMER_MAX_TICKS - counter_regs->current_value1);

    /* Account for potential pending counter IRQ */
    // if (counter_regs->intclr == 1) {
    //     value_h += 1;
    //     value_l = (uint64_t)(RK3568_TIMER_MAX_TICKS - counter_regs->value);
    // }

    uint64_t value_ticks = (value_h << 32) | value_l;

    /* convert from ticks to nanoseconds */
    uint64_t value_whole_seconds = value_ticks / RK3568_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ticks = value_ticks % RK3568_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ns = (value_subsecond_ticks * NS_IN_S) / RK3568_TIMER_TICKS_PER_SECOND;
    uint64_t value_ns = value_whole_seconds * NS_IN_S + value_subsecond_ns;

    return value_ns;
}

void set_timeout(uint64_t curr_time, uint64_t timeout)
{
    timeout_regs->control = RK3568_TIMER_DISABLE;

    uint64_t ns = timeout - curr_time;
    uint64_t ticks_whole_seconds = (ns / NS_IN_S) * RK3568_TIMER_TICKS_PER_SECOND;
    uint64_t ticks_remainder = (ns % NS_IN_S) * RK3568_TIMER_TICKS_PER_SECOND / NS_IN_S;
    uint64_t num_ticks = ticks_whole_seconds + ticks_remainder;

    // if (num_ticks > RK3568_TIMER_MAX_TICKS) {
    //     /* truncate num_ticks to maximum timeout, will use multiple interrupts to process the requested timeout. */
    //     num_ticks = RK3568_TIMER_MAX_TICKS;
    // }

    timeout_regs->load_count0 = num_ticks & 0xffffffff;
    timeout_regs->load_count1 = (num_ticks << 32);
    timeout_regs->control = RK3568_TIMER_ENABLE | RK3568_TIMER_ENABLE_IRQ | RK3568_TIMER_USER_DEFINED;
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
        set_timeout(curr_time, next_timeout);
    }
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    /* Ack any IRQs that were delivered before the driver started. */
    for (int i = 0; i < device_resources.num_irqs; i++) {
        microkit_irq_ack(device_resources.irqs[i].id);
    }

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    counter_irq = device_resources.irqs[0].id;
    timeout_irq = device_resources.irqs[1].id;

    uintptr_t timer_base = (uintptr_t)device_resources.regions[0].region.vaddr;
    counter_regs = (volatile rk3568_timer_regs_t *)timer_base;
    timeout_regs = (volatile rk3568_timer_regs_t *)(timer_base + RK3568_TIMER_SIZE);

    timeout_regs->control = (RK3568_TIMER_DISABLE | RK3568_TIMER_USER_DEFINED | RK3568_TIMER_ENABLE_IRQ);
    timeout_regs->load_count0 = RK3568_TIMER_MAX_TICKS;
    timeout_regs->load_count1 = RK3568_TIMER_MAX_TICKS;

    counter_regs->control = RK3568_TIMER_DISABLE | RK3568_TIMER_USER_DEFINED | RK3568_TIMER_ENABLE_IRQ;
    counter_regs->load_count0 = RK3568_TIMER_MAX_TICKS;
    counter_regs->load_count1 = RK3568_TIMER_MAX_TICKS;

    counter_regs->control = RK3568_TIMER_ENABLE;
}

void notified(microkit_channel ch)
{
    if (ch == counter_irq) {
        // TODO:
        assert(false);
        // counter_timer_elapses += 1;
        // while (counter_regs->intclr & STARFIVE_TIMER_INTCLR_BUSY) {
        //     /*
        //     * Hardware will not currently accept writes to this register.
        //     * Wait for this bit to be unset by hardware.
        //     */
        // }
        // counter_regs->intclr = 1;
    } else if (ch == timeout_irq) {
        // while (timeout_regs->intclr & STARFIVE_TIMER_INTCLR_BUSY) {
        //     /*
        //     * Hardware will not currently accept writes to this register.
        //     * Wait for this bit to be unset by hardware.
        //     */
        // }
        // timeout_regs->intclr = 1;

        timeout_regs->control = RK3568_TIMER_DISABLE;

        uint64_t curr_time = get_ticks_in_ns();
        process_timeouts(curr_time);
    } else {
        sddf_dprintf("TIMER DRIVER|LOG: unexpected notification from channel %u\n", ch);
        return;
    }

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
        uint64_t offset_ns = (uint64_t)(seL4_GetMR(0));
        timeouts[ch] = curr_time + offset_ns;
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
