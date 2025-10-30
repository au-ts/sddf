/*
    sddf_dprintf("TIMER DRIVER|LOG: regs load_count0 : %lu\n", timer->load_count0);
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

#define CLIENT_CH_START 2
#define MAX_TIMEOUTS 6

#define RK3568_TIMER_CONTROL_TIMER_ENABLE BIT(0)
#define RK3568_TIMER_CONTROL_MODE_USER BIT(1)
#define RK3568_TIMER_CONTROL_INTERRUPT_ENABLE BIT(2)

/* 24 MHz frequency. */
#define RK3568_TIMER_TICKS_PER_SECOND 0x16e3600

typedef struct {
    uint32_t load_count0;
    uint32_t load_count1;
    uint32_t current_value0;
    uint32_t current_value1;
    uint32_t control_reg;
    uint32_t reserved0;
    uint32_t int_status;
    uint32_t reserved1;
} rk3568_timer_regs_t;

static volatile rk3568_timer_regs_t * timestamp_timer;
static volatile rk3568_timer_regs_t * timeout_timer;
sddf_channel timestamp_irq;
sddf_channel timeout_irq;

/* Keep track of how many timer overflows have occured.
 * Used as the most significant segment of ticks.
 * We need to keep track of this state as the value register is only
 * 32 bits as opposed to the common 64 bit timer value regsiters found
 * on other devices.
 */
static uint64_t timeouts[MAX_TIMEOUTS];

static void print_regs(volatile rk3568_timer_regs_t * timer) {
    sddf_dprintf("TIMER DRIVER|LOG: regs load_count0 : 0x%x\n", timer->load_count0);
    sddf_dprintf("TIMER DRIVER|LOG: regs load_count1 : 0x%x\n", timer->load_count1);
    sddf_dprintf("TIMER DRIVER|LOG: regs current_value0: 0x%x\n", timer->current_value0);
    sddf_dprintf("TIMER DRIVER|LOG: regs current_value1: 0x%x\n", timer->current_value1);
    sddf_dprintf("TIMER DRIVER|LOG: regs control_reg: 0x%x\n", timer->control_reg);
    sddf_dprintf("TIMER DRIVER|LOG: regs int_status: 0x%x\n", timer->int_status);
}

static inline uint64_t get_ticks_in_ns(void)
{
    /* the timer value counts down from the load value */
    uint64_t load_values = timestamp_timer->current_value0;
    load_values |= (uint64_t)timestamp_timer->current_value1 << 32;
    uint64_t ticks = UINT64_MAX - load_values;

    /* convert from ticks to nanoseconds */
    uint64_t value_whole_seconds = ticks / RK3568_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ticks = ticks % RK3568_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ns = (value_subsecond_ticks * NS_IN_S) / RK3568_TIMER_TICKS_PER_SECOND;
    uint64_t value_ns = value_whole_seconds * NS_IN_S + value_subsecond_ns;

    sddf_dprintf("TIMER DRIVER|LOG: get_ticks_in_ns load_values: %lu value_ns: %lu\n", load_values, value_ns);
    return value_ns;
}

void set_timeout(uint64_t ns)
{
    //sddf_dprintf("TIMER DRIVER|LOG: TIMEOUT SET_TIMEOUT\n");
    //print_regs(timeout_timer);
    /* load the timeout timer with ticks to count down from */
    uint64_t ticks_whole_seconds = (ns / NS_IN_S) * RK3568_TIMER_TICKS_PER_SECOND;
    uint64_t ticks_remainder = (ns % NS_IN_S) * RK3568_TIMER_TICKS_PER_SECOND;
    uint64_t num_ticks = ticks_whole_seconds + ticks_remainder;
    uint32_t timeout_ticks_l = num_ticks & 0x00000000ffffffff;
    uint32_t timeout_ticks_h = num_ticks & 0xffffffff00000000;

    timeout_timer->control_reg = 0x0;

    timeout_timer->load_count0 = timeout_ticks_l;
    timeout_timer->load_count1 = timeout_ticks_h;

    timeout_timer->control_reg = (RK3568_TIMER_CONTROL_TIMER_ENABLE |
                                  RK3568_TIMER_CONTROL_MODE_USER |
                                  RK3568_TIMER_CONTROL_INTERRUPT_ENABLE);
    //sddf_dprintf("TIMER DRIVER|LOG: set_timeout timeout_ns: %lu ticks: %lu\n", ns, num_ticks);
    //print_regs(timeout_timer);
    return;
}

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            sddf_notify(CLIENT_CH_START + i);
            timeouts[i] = UINT64_MAX;
        }
    }

    uint64_t next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] < next_timeout) {
            next_timeout = timeouts[i];
        }
    }
    //sddf_dprintf("TIMER DRIVER|LOG: process timeout val: %lu curr_time: %lu\n", timeout, curr_time);
    uint64_t ns = next_timeout - curr_time;
    //sddf_dprintf("TIMER DRIVER|LOG: next timeout in %lu\n", ns);
    set_timeout(ns);

    return;
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    sddf_dprintf("Touch mem region phys 0x%lx vaddr: %p\n", device_resources.regions[0].io_addr, (uint64_t*)device_resources.regions[0].region.vaddr);
    sddf_dprintf("0x%lx\n", *((uint64_t*)device_resources.regions[0].region.vaddr));

    /* Ack any IRQs that were delivered before the driver started. */
    for (int i = 0; i < device_resources.num_irqs; i++) {
        sddf_irq_ack(device_resources.irqs[i].id);
    }

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    timestamp_timer = device_resources.regions[0].region.vaddr;
    timeout_timer = device_resources.regions[0].region.vaddr + sizeof(rk3568_timer_regs_t);

    // Start programming
    timestamp_timer->control_reg = 0x0;
    timeout_timer->control_reg = 0x0;

    // Set the respective modes
    timestamp_timer->control_reg = RK3568_TIMER_CONTROL_INTERRUPT_ENABLE;
    timeout_timer->control_reg = (RK3568_TIMER_CONTROL_MODE_USER | RK3568_TIMER_CONTROL_INTERRUPT_ENABLE);

    timestamp_timer->load_count0 = 0xffffffff;
    timestamp_timer->load_count1 = 0xffffffff;

    // Initially timeout timer is in timeout, has to be reset manually
    timeout_timer->load_count0 = 0x0;
    timeout_timer->load_count1 = 0x0;

    timestamp_irq = device_resources.irqs[0].id;
    timeout_irq = device_resources.irqs[1].id;

    timestamp_timer->control_reg |= RK3568_TIMER_CONTROL_TIMER_ENABLE;

    //sddf_dprintf("TIMER DRIVER|LOG: INIT\n");
    //print_regs(timestamp_timer);
    //sddf_dprintf("TIMER DRIVER|LOG: INIT2\n");
    //print_regs(timeout_timer);
}

void notified(sddf_channel ch)
{
    if (ch == timestamp_irq) {
        sddf_dprintf("TIMER DRIVER|LOG: notified on timestamp_irq channel\n");
        // we don't really care about that right now
    } else if (ch == timeout_irq) {
        //sddf_dprintf("TIMER DRIVER|LOG: notified on timeout channel %u\n", ch);
        //print_regs(timeout_timer);
        /* acknowledge the interrupt and disable the timer */
        timeout_timer->int_status = 0x1;
        timeout_timer->control_reg ^= RK3568_TIMER_CONTROL_TIMER_ENABLE;
        //print_regs(timeout_timer);
        sddf_notify(CLIENT_CH_START);
    } else {
        sddf_dprintf("TIMER DRIVER|LOG: unexpected notification from channel %u\n", ch);
    }
    sddf_deferred_irq_ack(ch);
}

seL4_MessageInfo_t protected(sddf_channel ch, seL4_MessageInfo_t msginfo)
{
    // TODO: add timestamp/timeout channel handling
    switch (seL4_MessageInfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        uint64_t time_ns = get_ticks_in_ns(); //XXX
        sddf_set_mr(0, time_ns);
        return seL4_MessageInfo_new(0, 0, 0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = get_ticks_in_ns();
        uint64_t offset_ns = (uint64_t)(sddf_get_mr(0));
        timeouts[ch - CLIENT_CH_START] = curr_time + offset_ns;
        process_timeouts(curr_time);
        break;
    }
    default:
        sddf_dprintf("TIMER DRIVER|LOG: Unknown request %lu to timer from channel %u\n",
                     seL4_MessageInfo_get_label(msginfo), ch);
        break;
    }

    return seL4_MessageInfo_new(0, 0, 0, 0);
}
