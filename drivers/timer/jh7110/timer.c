/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/resources/device.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/timer/timer_driver.h>

/*
 * The JH7110 SoC contains a timer with four 32-bit counters. Each one of these
 * counters is referred to as a "channel". These are not to be confused with
 * channels between the driver and clients. Anything with a prefix
 * STARFIVE_TIMER_* is to do with the hardware.
 */
#define STARFIVE_TIMER_NUM_CHANNELS 4

#define STARFIVE_TIMER_CHANNEL_REGS_SIZE 0x40

#ifndef STARFIVE_TIMER_CHANNEL
#define STARFIVE_TIMER_CHANNEL 1
#endif

#if STARFIVE_TIMER_CHANNEL >= STARFIVE_TIMER_NUM_CHANNELS
#error "Invalid StarFive timer device channel"
#endif

#define CLIENT_CH_START 2
#define MAX_TIMEOUTS SDDF_TIMER_MAX_CLIENTS

#define STARFIVE_TIMER_MAX_TICKS UINT32_MAX
#define STARFIVE_TIMER_MODE_CONTINUOUS 0
#define STARFIVE_TIMER_MODE_SINGLE 1
#define STARFIVE_TIMER_DISABLED 0
#define STARFIVE_TIMER_ENABLED 1
#define STARFIVE_TIMER_INTERRUPT_UNMASKED 0
#define STARFIVE_TIMER_INTERRUPT_MASKED 1
#define STARFIVE_TIMER_INTCLR_BUSY (1 << 1)

#if defined(CONFIG_PLAT_STAR64)
/* 24 MHz frequency. */
#define JH7110_CLK_FREQ 0x16e3600
#else
#error "Unknown clock-frequency for JH7110 timer"
#endif

typedef struct {
    /* Registers */
    uint32_t intstatus; /* 0x00: Interrupt status for channels 0 -4. Read only. */
    uint32_t ctrl;      /* 0x04: Timer control. 0 - continuous run, 1 - single run. */
    uint32_t load;      /* 0x08: Load value to counter. */
    uint32_t unknown1;  /* 0x0b: Unused. */
    uint32_t enable;    /* 0x10: Timer enable register. */
    uint32_t reload;    /* 0x14: Write 1 or 0, both reload counter. */
    uint32_t value;     /* 0x18: Value of timer. Read only. */
    uint32_t unknown2;  /* 0x1b: Unused. */
    uint32_t intclr;    /* 0x20: Timer interrupt clear register. */
    uint32_t intmask;   /* 0x24: Timer interrupt mask register. */
} starfive_timer_regs_t;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".timer_driver_config"))) timer_driver_config_t config;

static volatile starfive_timer_regs_t *counter_regs;
static volatile starfive_timer_regs_t *timeout_regs;
sddf_channel counter_irq;
sddf_channel timeout_irq;

/* Keep track of how many timer overflows have occured.
 * Used as the most significant segment of ticks.
 * We need to keep track of this state as the value register is only
 * 32 bits as opposed to the common 64 bit timer value regsiters found
 * on other devices.
 */
uint32_t counter_timer_elapses = 0;
uint32_t timeout_timer_elapses = 0;

/* Right now, we only service a single timeout per client.
 * This timeout array indicates when a timeout should occur,
 * indexed by client ID. */
static uint64_t target_timeout = UINT64_MAX;

static uint64_t get_ticks_in_ns(void)
{
    /* the timer value counts down from the load value */
    uint64_t value_l = (uint64_t)(STARFIVE_TIMER_MAX_TICKS - counter_regs->value);
    uint64_t value_h = (uint64_t)counter_timer_elapses;

    /* Account for potential pending counter IRQ */
    if (counter_regs->intclr == 1) {
        value_h += 1;
        value_l = (uint64_t)(STARFIVE_TIMER_MAX_TICKS - counter_regs->value);
    }

    uint64_t value_ticks = (value_h << 32) | value_l;

    return tick_to_ns_cached(value_ticks, 0, JH7110_CLK_FREQ);
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
        timeout_regs->enable = STARFIVE_TIMER_DISABLED;
        timeout_timer_elapses = 0;
        timeout_regs->ctrl = STARFIVE_TIMER_MODE_SINGLE;

        uint64_t num_ticks = ns_to_tick_cached(ns, 0, JH7110_CLK_FREQ);

        if (num_ticks > STARFIVE_TIMER_MAX_TICKS) {
            /* truncate num_ticks to maximum timeout, will use multiple interrupts to process the requested timeout. */
            num_ticks = STARFIVE_TIMER_MAX_TICKS;
        }

        timeout_regs->load = num_ticks;
        timeout_regs->enable = STARFIVE_TIMER_ENABLED;
    }
}

void notified(sddf_channel ch)
{
    if (ch == counter_irq) {
        counter_timer_elapses += 1;
        while (counter_regs->intclr & STARFIVE_TIMER_INTCLR_BUSY) {
            /*
            * Hardware will not currently accept writes to this register.
            * Wait for this bit to be unset by hardware.
            */
        }
        counter_regs->intclr = 1;
    } else if (ch == timeout_irq) {
        timeout_timer_elapses += 1;
        while (timeout_regs->intclr & STARFIVE_TIMER_INTCLR_BUSY) {
            /*
            * Hardware will not currently accept writes to this register.
            * Wait for this bit to be unset by hardware.
            */
        }
        timeout_regs->intclr = 1;

        uint64_t curr_time = get_ticks_in_ns();
       process_target_timeout(curr_time);
    } else {
        sddf_dprintf("TIMER DRIVER|LOG: unexpected notification from channel %u\n", ch);
        return;
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

void init(void)
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    counter_irq = device_resources.irqs[0].id;
    timeout_irq = device_resources.irqs[1].id;

    uintptr_t timer_base = (uintptr_t)device_resources.regions[0].region.vaddr;
    counter_regs = (volatile starfive_timer_regs_t *)timer_base;
    timeout_regs = (volatile starfive_timer_regs_t *)(timer_base
                                                      + STARFIVE_TIMER_CHANNEL_REGS_SIZE * STARFIVE_TIMER_CHANNEL);
    timeout_regs->enable = STARFIVE_TIMER_DISABLED;
    timeout_regs->ctrl = STARFIVE_TIMER_MODE_CONTINUOUS;
    timeout_regs->load = STARFIVE_TIMER_MAX_TICKS;
    timeout_regs->intmask = STARFIVE_TIMER_INTERRUPT_UNMASKED;

    counter_regs->enable = STARFIVE_TIMER_DISABLED;
    counter_regs->ctrl = STARFIVE_TIMER_MODE_CONTINUOUS;
    counter_regs->load = STARFIVE_TIMER_MAX_TICKS;
    counter_regs->intmask = STARFIVE_TIMER_INTERRUPT_UNMASKED;

    counter_regs->enable = STARFIVE_TIMER_ENABLED;
}
