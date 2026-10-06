/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

#define MAX_TIMEOUTS SDDF_TIMER_MAX_CLIENTS

#define RK3399_TIMER_CONTROL_TIMER_ENABLE BIT(0)
#define RK3399_TIMER_CONTROL_MODE_USER BIT(1)
#define RK3399_TIMER_CONTROL_INTERRUPT_ENABLE BIT(2)
#define RK3399_TIMER_IRQ_ACK BIT(0)

/* 24 MHz frequency. */
#define RK3399_TIMER_FREQUENCY ((uint64_t)24000000)

typedef struct {
    uint32_t load_count0;
    uint32_t load_count1;
    uint32_t current_value0;
    uint32_t current_value1;
    uint32_t load_count2;
    uint32_t load_count3;
    uint32_t int_status;
    uint32_t control_reg;
} rk3399_timer_regs_t;

static volatile rk3399_timer_regs_t *timestamp_timer;
static volatile rk3399_timer_regs_t *timeout_timer;
sddf_channel timeout_irq;

static uint64_t timeouts[MAX_TIMEOUTS];

static inline void acknowledge_irq(void)
{
    timeout_timer->int_status = RK3399_TIMER_IRQ_ACK;
    timeout_timer->control_reg ^= RK3399_TIMER_CONTROL_TIMER_ENABLE;
}

static inline uint64_t get_ticks_in_ns(void)
{
    /* the timer value counts up from the load value */
    uint64_t value_h1 = timestamp_timer->current_value1;
    uint64_t value_l = timestamp_timer->current_value0;

    /* detects and handles counter overflows between reading the lower and upper halves */
    uint64_t value_h2 = timestamp_timer->current_value1;
    if (value_h2 != value_h1) {
        value_l = timestamp_timer->current_value0;
    }
    uint64_t ticks = ((uint64_t)value_h2 << 32) | value_l;

    return ticks_to_ns(ticks, RK3399_TIMER_FREQUENCY);
}

void set_timeout(uint64_t ns)
{
    /* load the timeout timer with ticks to count up from */
    uint64_t num_ticks = ns_to_ticks(ns, RK3399_TIMER_FREQUENCY);
    uint32_t timeout_ticks_l = (uint32_t)num_ticks;
    uint32_t timeout_ticks_h = (uint32_t)(num_ticks >> 32);

    timeout_timer->control_reg = 0x0;

    timeout_timer->load_count0 = timeout_ticks_l;
    timeout_timer->load_count1 = timeout_ticks_h;

    timeout_timer->control_reg = (RK3399_TIMER_CONTROL_TIMER_ENABLE | RK3399_TIMER_CONTROL_MODE_USER
                                  | RK3399_TIMER_CONTROL_INTERRUPT_ENABLE);
    LOG_TIMER_DRIVER("set_timeout timeout_ns: %lu ticks: %lu\n", ns, num_ticks);
}

static void process_timeouts(uint64_t curr_time)
{
    LOG_TIMER_DRIVER("process timeouts curr_time: %lu\n", curr_time);
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            sddf_notify(device_resources.num_irqs + i);
            timeouts[i] = UINT64_MAX;
        }
    }

    uint64_t next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] < next_timeout) {
            LOG_TIMER_DRIVER("next timeout at %lu i=%d\n", timeouts[i], i);
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
    for (int i = 0; i < device_resources.num_irqs; i++) {
        sddf_irq_ack(device_resources.irqs[i].id);
    }

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    timeout_timer = device_resources.regions[0].region.vaddr;
    timestamp_timer = device_resources.regions[0].region.vaddr + sizeof(rk3399_timer_regs_t);

    /* Start programming */
    timestamp_timer->control_reg = 0x0;
    timeout_timer->control_reg = 0x0;

    /* The timer counts up from <count3, count2> to <count1, count0> */
    timestamp_timer->load_count3 = 0;
    timestamp_timer->load_count2 = 0;
    timestamp_timer->load_count1 = UINT32_MAX;
    timestamp_timer->load_count0 = UINT32_MAX;

    timeout_timer->load_count3 = 0;
    timeout_timer->load_count2 = 0;

    timeout_irq = device_resources.irqs[0].id;

    timestamp_timer->control_reg |= RK3399_TIMER_CONTROL_TIMER_ENABLE;
}

void notified(sddf_channel ch)
{
    if (ch == timeout_irq) {
        /* acknowledge the interrupt and disable the timer */
        acknowledge_irq();
        process_timeouts(get_ticks_in_ns());
    } else {
        LOG_TIMER_DRIVER_ERR("unexpected notification from channel %u\n", ch);
    }
    sddf_deferred_irq_ack(ch);
}

seL4_MessageInfo_t protected(sddf_channel ch, seL4_MessageInfo_t msginfo)
{
    switch (seL4_MessageInfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        sddf_set_mr(0, get_ticks_in_ns());
        return seL4_MessageInfo_new(0, 0, 0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = get_ticks_in_ns();
        uint64_t offset_ns = (uint64_t)(sddf_get_mr(0));
        timeouts[ch - device_resources.num_irqs] = curr_time + offset_ns;
        process_timeouts(curr_time);
        break;
    }
    default:
        LOG_TIMER_DRIVER_ERR("Unknown request %lu to timer from channel %u\n", seL4_MessageInfo_get_label(msginfo), ch);
        break;
    }

    return seL4_MessageInfo_new(0, 0, 0, 0);
}
