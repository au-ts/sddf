/*
 * Copyright 2025, UNSW
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
__attribute__((__section__(".timer_driver_config"))) timer_driver_config_t config;

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

static uint64_t target_timeout = UINT64_MAX;

static void print_regs(volatile rk3568_timer_regs_t *timer)
{
    LOG_TIMER_DRIVER("regs load_count0 : 0x%x\n", timer->load_count0);
    LOG_TIMER_DRIVER("regs load_count1 : 0x%x\n", timer->load_count1);
    LOG_TIMER_DRIVER("regs current_value0: 0x%x\n", timer->current_value0);
    LOG_TIMER_DRIVER("regs current_value1: 0x%x\n", timer->current_value1);
    LOG_TIMER_DRIVER("regs control_reg: 0x%x\n", timer->control_reg);
    LOG_TIMER_DRIVER("regs int_status: 0x%x\n", timer->int_status);
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

    return tick_to_ns_cached(ticks, 0, RK3568_TIMER_FREQUENCY);
}

void set_timeout(uint64_t ns)
{
    /* load the timeout timer with ticks to count down from */
    uint64_t num_ticks = ns_to_tick_cached(ns, 0, RK3568_TIMER_FREQUENCY);
    uint32_t timeout_ticks_l = (uint32_t)num_ticks;
    uint32_t timeout_ticks_h = (uint32_t)(num_ticks >> 32);

    timeout_timer->control_reg = 0x0;

    timeout_timer->load_count0 = timeout_ticks_l;
    timeout_timer->load_count1 = timeout_ticks_h;

    timeout_timer->control_reg = (RK3568_TIMER_CONTROL_TIMER_ENABLE | RK3568_TIMER_CONTROL_MODE_USER
                                  | RK3568_TIMER_CONTROL_INTERRUPT_ENABLE);
    LOG_TIMER_DRIVER("set_timeout timeout_ns: %lu ticks: %lu\n", ns, num_ticks);
    return;
}

static void process_target_timeout(uint64_t curr_time)
{
    if (target_timeout <= curr_time) {
        sddf_notify(config.virt_id);
        // Update "current" time page with virt
        set_shared_time_page(get_current_time());
        target_timeout = UINT64_MAX;
    }

    if (target_timeout != UINT64_MAX) {
        uint64_t ns = target_timeout - curr_time;
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
        process_target_timeout(get_ticks_in_ns());
    } else {
        LOG_TIMER_DRIVER_ERR("unexpected notification from channel %u\n", ch);
    }
    sddf_deferred_irq_ack(ch);
}

// Protocol common functions
bool set_new_timeout(uint64_t timestamp)
{
    uint64_t curr_time_ns = get_ticks_in_ns();
    // Convert to ticks and set as target
    target_timeout = timestamp;
    LOG_TIMER_DRIVER("Setting timeout for %zu ns\n", target_timeout);

    process_target_timeout(curr_time_ns);
    return true;
}

uint64_t get_current_time(void)
{
    return get_ticks_in_ns();
}
