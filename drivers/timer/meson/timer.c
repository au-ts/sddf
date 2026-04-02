/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/timer/timer_driver.h>

#define MAX_TIMEOUTS SDDF_TIMER_MAX_CLIENTS

#define TIMER_REG_START   0x70    // TIMER_MUX

#define TIMER_A_INPUT_CLK 0
#define TIMER_E_INPUT_CLK 8
#define TIMER_A_EN      (1 << 16)
#define TIMER_A_MODE    (1 << 12)

#define TIMESTAMP_TIMEBASE_SYSTEM   0b000
#define TIMESTAMP_TIMEBASE_1_US     0b001
#define TIMESTAMP_TIMEBASE_10_US    0b010
#define TIMESTAMP_TIMEBASE_100_US   0b011
#define TIMESTAMP_TIMEBASE_1_MS     0b100

#define TIMEOUT_TIMEBASE_1_US   0b00
#define TIMEOUT_TIMEBASE_10_US  0b01
#define TIMEOUT_TIMEBASE_100_US 0b10
#define TIMEOUT_TIMEBASE_1_MS   0b11

// We hard code 1us timebase. 1us^-1 = 1MHz.
// Change this if the timebase changes!
#define MESON_TIMER_CLK_FREQ ((sddf_timer_freq_hz_t) 1*MEGA)

__attribute__((__section__(".timer_driver_config"))) timer_driver_config_t config;
__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

struct timer_regs {
    uint32_t mux;
    uint32_t timer_a;
    uint32_t timer_b;
    uint32_t timer_c;
    uint32_t timer_d;
    uint32_t unused[13];
    uint32_t timer_e;
    uint32_t timer_e_hi;
    uint32_t mux1;
    uint32_t timer_f;
    uint32_t timer_g;
    uint32_t timer_h;
    uint32_t timer_i;
};

volatile struct timer_regs *regs;
static uint64_t target_timeout = UINT64_MAX;

static uint64_t get_ticks(void)
{
    uint64_t initial_high = regs->timer_e_hi;
    uint64_t low = regs->timer_e;
    uint64_t high = regs->timer_e_hi;
    if (high != initial_high) {
        low = regs->timer_e;
    }

    uint64_t ticks = (high << 32) | low;
    return ticks;
}

static void process_timeouts(uint64_t curr_time)
{
    if (target_timeout <= curr_time) {
        sddf_notify(config.virt_id);
        // Update "current" time page with virt
        set_shared_time_page(get_current_time());
        target_timeout = UINT64_MAX;
    }

    if (target_timeout != UINT64_MAX) {
        regs->mux &= ~TIMER_A_MODE;
        regs->timer_a = target_timeout - curr_time;
        regs->mux |= TIMER_A_EN;
    }
}

bool set_new_timeout(uint64_t timestamp)
{
    uint64_t curr_time = get_ticks();
    // Convert to ticks and set as target
    target_timeout = ns_to_tick_cached(timestamp, 0, (sddf_timer_freq_hz_t) MESON_TIMER_CLK_FREQ);
    LOG_TIMER_DRIVER("Setting timeout for %zu ticks\n", target_timeout);

    process_timeouts(curr_time);
    return true;
}

uint64_t get_current_time(void)
{
    return (tick_to_ns_cached(get_ticks(), 0, (sddf_timer_freq_hz_t) MESON_TIMER_CLK_FREQ));
}

void notified(sddf_channel ch)
{
    if (ch != device_resources.irqs[0].id) {
        sddf_dprintf("TIMER DRIVER|LOG: unexpected notification from channel %u\n", ch);
        return;
    }

    sddf_deferred_irq_ack(ch);
    regs->mux &= ~TIMER_A_EN;

    uint64_t curr_time = get_ticks();
    process_timeouts(curr_time);
}

void init(void)
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    regs = (void *)((uintptr_t)device_resources.regions[0].region.vaddr + TIMER_REG_START);

    /* Start timer E acts as a clock, while timer A can be used for timeouts from clients */
    regs->mux = TIMER_A_EN | (TIMESTAMP_TIMEBASE_1_US << TIMER_E_INPUT_CLK) |
                (TIMEOUT_TIMEBASE_1_US << TIMER_A_INPUT_CLK);

    regs->timer_e = 0;
}
