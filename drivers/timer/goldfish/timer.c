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

// This is a virtual timer - it has no clock rate and just returns nanoseconds directly.
// This is equivalent to a 1GHz clock, but we don't attempt time conversion here since
// it would be pointless.

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
__attribute__((__section__(".timer_driver_config"))) timer_driver_config_t config;
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

static uint64_t target_timeout = UINT64_MAX;

static void process_target_timeout(uint64_t curr_time_ns)
{
    if (target_timeout <= curr_time_ns) {
        sddf_notify(config.virt_id);
        // Update "current" time page with virt
        set_shared_time_page(get_current_time());
        target_timeout = UINT64_MAX;
    }

    if (target_timeout != UINT64_MAX) {
        set_timeout(target_timeout);
    }
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);
    timer_regs = (goldfish_timer_regs_t *)device_resources.regions[0].region.vaddr;
}

void notified(sddf_channel ch)
{
    assert(ch == device_resources.irqs[0].id);
    sddf_deferred_irq_ack(ch);

    /* Handled irq -> clear device interrupt */
    timer_regs->clear_interrupt = 1;
    uint64_t curr_time = get_ticks_in_ns();
    process_target_timeout(curr_time);
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
