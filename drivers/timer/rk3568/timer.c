/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

//#define DEBUG_TIMER

#ifdef DEBUG_TIMER
#define LOG_TIMER(...) do{ sddf_printf("LOG_TIMER|INFO: ");sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_TIMER(...) do{}while(0)
#endif // DEBUG_TIMER

#define LOG_TIMER_ERR(...) do{ sddf_printf("LOG_TIMER|ERROR: ");sddf_printf(__VA_ARGS__); }while(0)

#define MAX_TIMEOUTS SDDF_TIMER_MAX_CLIENTS

#define RK3568_TIMER_CONTROL_TIMER_ENABLE BIT(0)
#define RK3568_TIMER_CONTROL_MODE_USER BIT(1)
#define RK3568_TIMER_CONTROL_INTERRUPT_ENABLE BIT(2)
#define RK3568_TIMER_IRQ_ACK 0x1

/* 24 MHz frequency. */
#define RK3568_TIMER_FREQUENCY ((uint64_t)24000000)
#define NANO_INVERSE NS_IN_S

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

static volatile rk3568_timer_regs_t *timestamp_timer;
static volatile rk3568_timer_regs_t *timeout_timer;
sddf_channel timestamp_irq;
sddf_channel timeout_irq;

static uint64_t timeouts[MAX_TIMEOUTS];

static void print_regs(volatile rk3568_timer_regs_t *timer)
{
    LOG_TIMER("regs load_count0 : 0x%x\n", timer->load_count0);
    LOG_TIMER("regs load_count1 : 0x%x\n", timer->load_count1);
    LOG_TIMER("regs current_value0: 0x%x\n", timer->current_value0);
    LOG_TIMER("regs current_value1: 0x%x\n", timer->current_value1);
    LOG_TIMER("regs control_reg: 0x%x\n", timer->control_reg);
    LOG_TIMER("regs int_status: 0x%x\n", timer->int_status);
}

static inline void acknowledge_irq(void)
{
    timeout_timer->int_status = RK3568_TIMER_IRQ_ACK;
    timeout_timer->control_reg ^= RK3568_TIMER_CONTROL_TIMER_ENABLE;
}

static inline uint64_t get_ticks_in_ns(void)
{
    /* the timer value counts down from the load value */
    uint64_t load_values = timestamp_timer->current_value0;
    load_values |= (uint64_t)timestamp_timer->current_value1 << 32;
    uint64_t ticks = UINT64_MAX - load_values;

    /* convert from ticks to nanoseconds */
    uint64_t value_s = ticks / RK3568_TIMER_FREQUENCY;
    uint64_t value_frac = ticks % RK3568_TIMER_FREQUENCY;
    uint64_t value_ns = (value_s * NANO_INVERSE) + (value_frac * NANO_INVERSE) / RK3568_TIMER_FREQUENCY;

    LOG_TIMER("get_ticks_in_ns load_values: %lu value_ns: %lu\n", load_values, value_ns);
    return value_ns;
}

void set_timeout(uint64_t ns)
{
    /* load the timeout timer with ticks to count down from */
    uint64_t num_s = ns / NANO_INVERSE;
    uint64_t num_frac = ns % NANO_INVERSE;
    uint64_t num_ticks = (num_s * RK3568_TIMER_FREQUENCY) + (num_frac * RK3568_TIMER_FREQUENCY) / NANO_INVERSE;
    uint32_t timeout_ticks_l = (uint32_t)num_ticks;
    uint32_t timeout_ticks_h = (uint32_t)(num_ticks >> 32);

    timeout_timer->control_reg = 0x0;

    timeout_timer->load_count0 = timeout_ticks_l;
    timeout_timer->load_count1 = timeout_ticks_h;

    timeout_timer->control_reg = (RK3568_TIMER_CONTROL_TIMER_ENABLE | RK3568_TIMER_CONTROL_MODE_USER
                                  | RK3568_TIMER_CONTROL_INTERRUPT_ENABLE);
    LOG_TIMER("set_timeout timeout_ns: %lu ticks: %lu\n", ns, num_ticks);
    return;
}

static void process_timeouts(uint64_t curr_time)
{
    LOG_TIMER("process timeouts curr_time: %lu\n", curr_time);
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            sddf_notify(device_resources.num_irqs + i);
            timeouts[i] = UINT64_MAX;
        }
    }

    uint64_t next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] < next_timeout) {
            LOG_TIMER("next timeout at %lu i=%d\n", timeouts[i], i);
            next_timeout = timeouts[i];
        }
    }

    if (next_timeout != UINT64_MAX) {
        uint64_t ns = next_timeout - curr_time;
        set_timeout(ns);
    }

    return;
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    /* Ack any IRQs that were delivered before the driver started. */
    for (int i = 0; i < device_resources.num_irqs; i++) {
        sddf_irq_ack(device_resources.irqs[i].id);
    }

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    timestamp_timer = device_resources.regions[0].region.vaddr;
    timeout_timer = device_resources.regions[0].region.vaddr + sizeof(rk3568_timer_regs_t);

    /* Start programming */
    timestamp_timer->control_reg = 0x0;
    timeout_timer->control_reg = 0x0;

    /* Set the respective modes */
    timestamp_timer->control_reg = RK3568_TIMER_CONTROL_INTERRUPT_ENABLE;
    timeout_timer->control_reg = (RK3568_TIMER_CONTROL_MODE_USER | RK3568_TIMER_CONTROL_INTERRUPT_ENABLE);

    timestamp_timer->load_count0 = 0xffffffff;
    timestamp_timer->load_count1 = 0xffffffff;

    /* Initially timeout timer is in timeout, has to be reset manually */
    timeout_timer->load_count0 = 0x0;
    timeout_timer->load_count1 = 0x0;

    timestamp_irq = device_resources.irqs[0].id;
    timeout_irq = device_resources.irqs[1].id;

    timestamp_timer->control_reg |= RK3568_TIMER_CONTROL_TIMER_ENABLE;
}

void notified(sddf_channel ch)
{
    if (ch == timestamp_irq) {
        /* we don't care about that right now */
    } else if (ch == timeout_irq) {
        /* acknowledge the interrupt and disable the timer */
        acknowledge_irq();
        process_timeouts(get_ticks_in_ns());
    } else {
        LOG_TIMER_ERR("unexpected notification from channel %u\n", ch);
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
        LOG_TIMER_ERR("Unknown request %lu to timer from channel %u\n", seL4_MessageInfo_get_label(msginfo), ch);
        break;
    }

    return seL4_MessageInfo_new(0, 0, 0, 0);
}
