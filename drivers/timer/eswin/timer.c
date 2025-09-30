/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/timer/protocol.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

struct timer_regs {
    uint32_t load_count;
    uint32_t val;
    uint32_t ctrl;
    uint32_t eoi;
    uint32_t int_status;
};

void *regs_base;
volatile struct timer_regs *counter_timer_regs;
volatile struct timer_regs *timeout_timer_regs;

/* We use separate timers (but on the same hardware device) for the counter and setting timeouts. */
#define TIMER_COUNTER 1
#define TIMER_TIMEOUT 2

#define TIMER_N_OFFSET(n) ((n - 1) * 0x14)

#define LOAD_COUNT2(n) (0xb0 + TIMER_N_OFFSET(n))

#define REG_PTR(off)     ((volatile uint32_t *)((regs_base) + (off)))

// TODO: huh? why 6?
#define MAX_TIMEOUTS 6
static uint64_t timeouts[MAX_TIMEOUTS];

/* 24 MHz frequency. */
#define TIMER_TICKS_PER_SECOND 0x16e3600

#define TIMER_MAX_TICKS 0xffffffff

// TODO: remove
#define CLIENT_CH_START 1

/* Keep track of how many timer overflows have occured.
 * Used as the most significant segment of ticks.
 * We need to keep track of this state as the value register is only
 * 32 bits as opposed to the common 64 bit timer value regsiters found
 * on other devices.
 */
uint32_t counter_timer_elapses = 0;
uint32_t timeout_timer_elapses = 0;

static uint64_t get_ticks_in_ns(bool irq)
{
    /* the timer value counts down from the load value */
    uint32_t value_l = (TIMER_MAX_TICKS - counter_timer_regs->val);
    uint32_t value_h = counter_timer_elapses;

    /* Include unhandled interrupt in value_h */
    if (irq) {
        value_h += 1;
    }

    uint64_t value_ticks = ((uint64_t)value_h << 32) | value_l;

    /* convert from ticks to nanoseconds */
    uint64_t value_whole_seconds = value_ticks / TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ticks = value_ticks % TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ns = (value_subsecond_ticks * NS_IN_S) / TIMER_TICKS_PER_SECOND;
    uint64_t value_ns = value_whole_seconds * NS_IN_S + value_subsecond_ns;

    return value_ns;
}

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            microkit_notify(CLIENT_CH_START + i);
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
        timeout_timer_regs->ctrl &= 0xfffffffe;
        timeout_timer_regs->ctrl |= (1 << 1);

        timeout_timer_elapses = 0;

        uint64_t ticks_whole_seconds = (ns / NS_IN_S) * TIMER_TICKS_PER_SECOND;
        uint64_t ticks_remainder = (ns % NS_IN_S) * TIMER_TICKS_PER_SECOND / NS_IN_S;
        uint64_t num_ticks = ticks_whole_seconds + ticks_remainder;

        assert(num_ticks <= TIMER_TICKS_PER_SECOND);
        if (num_ticks > TIMER_TICKS_PER_SECOND) {
            sddf_dprintf("ERROR: num_ticks: 0x%lx\n", num_ticks);
        }

        timeout_timer_regs->load_count = num_ticks;
        *REG_PTR(LOAD_COUNT2(TIMER_TIMEOUT)) = 0x0;
        timeout_timer_regs->ctrl |= (1 << 0);
    }
}

void notified(microkit_channel ch)
{
    assert(ch == device_resources.irqs[0].id);

    if (counter_timer_regs->int_status & 0x1) {
        counter_timer_elapses += 1;
        counter_timer_regs->eoi;
    }

    if (timeout_timer_regs->int_status & 0x1) {
        timeout_timer_elapses += 1;
        uint64_t curr_time = get_ticks_in_ns(true);
        process_timeouts(curr_time);
        timeout_timer_regs->eoi;
    }

    microkit_deferred_irq_ack(ch);
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        uint64_t time_ns = get_ticks_in_ns(false);
        seL4_SetMR(0, time_ns);
        return microkit_msginfo_new(0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = get_ticks_in_ns(false);
        uint64_t offset_ns = seL4_GetMR(0);
        timeouts[ch - CLIENT_CH_START] = curr_time + offset_ns;
        process_timeouts(curr_time);
        break;
    }
    default:
        sddf_dprintf("TIMER DRIVER|ERROR: Unknown request %lu to timer from channel %u\n",
                     microkit_msginfo_get_label(msginfo), ch);
        break;
    }

    return microkit_msginfo_new(0, 0);
}

void init(void)
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    counter_timer_regs = device_resources.regions[0].region.vaddr;
    timeout_timer_regs = device_resources.regions[0].region.vaddr + 0x14;
    regs_base = device_resources.regions[0].region.vaddr;

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    // Setup the counter timer

    // 1. Disable the timer
    counter_timer_regs->ctrl &= 0xfffffffe;
    // 2. Set mode to free-running
    counter_timer_regs->ctrl &= 0xfffffffd;
    counter_timer_regs->load_count = TIMER_MAX_TICKS;
    // 3. Enable timer
    counter_timer_regs->ctrl |= (1 << 0);
}
