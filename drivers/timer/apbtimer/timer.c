/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <cstdint>
#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/timer_driver.h>

#define NUM_TIMERS 2    // Adjust if synthesised with more timers.
                        // Minimum = 2 due to a bug in the HDL, assumed for rest of this driver.
#define MAX_TIMEOUTS (NUM_TIMERS)
#define APBTIMER_MAX_TICKS (UINT32_MAX)
#define APBTIMER_CLK_FREQ ((uint64_t)50000000) // 50MHz
#define NANO_INVERSE ((uint64_t)1000000000)

// The APB timer has an array of internal timers. Use one for long-running time measurements, use
// the other for generating interrupts at finer granularity using prescalers.
// TODO: support >2 timers; probably exposed over a different API for drivers etc?
#define TIMER_TIMEOUT    (0)
#define TIMER_TIMEKEEPER (1)

#define APBTIMER_CTRL_EN_BIT (BIT(0))
#define APBTIMER_CTRL_PRESCALER_SHIFT (3)
#define APBTIMER_CTRL_PRESCALER_MASK (0b111)    // *before* shift - see timer setup functions
#define APBTIMER_PRESCALER_MAX ((0xff & APBTIMER_CTRL_PRESCALER_MASK))

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

// Timer block implements NUM_TIMERS separate timers with back-to-back registers
struct timer_regs {
    uint32_t timer;
    uint32_t ctrl;
    uint32_t cmp;
};

// Array of regs structs, not just one set!
volatile struct timer_regs **regs;

/* Keep track of how many timer overflows have occured.
 * Used as the most significant segment of ticks.
 * We need to keep track of this state as the value register is only
 * 32 bits as opposed to the common 64 bit timer value regsiters found
 * on other devices.
 */
uint32_t timekeeper_overflow_count = 0;

// Priority heap for managing timeouts
static timer_heap_t timeouts = {0, 0};

typedef struct apbtimer_timeout_conf {
    uint32_t cmp;
    short prescaler;
} apbtimer_timeout_conf_t;

/**
 * Convert the tick count of a timer to nanoseconds, given the expected prescaler
 * and overflow counter. Prescaler can be set to 0 to ignore.
 *
 * Prescaler should be given in same format as ctrl reg - i.e. 0 = disabled (multiply
 * by 1), 1 = multiply by 2, etc.
 */
static inline uint64_t tick_to_ns(uint64_t ticks, short prescaler) {
    // seconds per tick = f_clk^-1
    // ns per tick = (f_clk^-1) / 1e9 = 1e9/f_clk
    // ticks in ns = ticks*(f_clk^-1) / 1e9 = (1e9 * ticks) / f_clk
    // with prescaler p, clock rate is divided. -> ns = (1e9 * ticks) / (f_clk * p)
    assert(prescaler <= APBTIMER_PRESCALER_MAX);
    short prescaler_adjusted = (prescaler == 0) ? 1: prescaler + 1;
    return (value_ticks * NANO_INVERSE) / (APBTIMER_CLK_FREQ * prescaler_adjusted);
}

/**
 * Return number of ticks since driver startup using timekeeper timer.
 * NOTE: one round of timer @ 50MHz with prescaler of (1<<3)=4 lasts for 171.8
 *          seconds. Time resolution = 80ns per tick.
 */
static uint64_t get_time_ns(void)
{
    uint64_t value_l = (uint64_t)(regs[TIMER_TIMEKEEPER]->timer);
    uint64_t value_h = (uint64_t)timekeeper_overflow_count;
    uint64_t value_ticks = (value_h << 32) | value_l;

    return tick_to_ns(value_ticks, APBTIMER_PRESCALER_MAX);
}

/**
 * Calculate the cmp value and prescaler for the timeout timer given
 * a desired delay in nanoseconds. If delay exceeds capacity of timer,
 * returns maximum prescaler and cmp.
 */
static apbtimer_timeout_conf_t calculate_timeout_from_ns(uint64_t ns_delay) {
    // Convert nanoseconds to ticks with a prescaler of zero (x1)
    // tick = 1 timer period = 1/f_clk
    // ticks = n. periods in delay = seconds_delay / f_clk
    //                             = ns_delay / (f_clk * 1000000000)
    uint64_t divisor = APBTIMER_CLK_FREQ * NANO_INVERSE;
    uint64_t ticks = ns_delay / divisor;

    uint32_t prescaler = 0;
    uint32_t cmp = 0;
    if (ticks <= UINT32_MAX) {
        // No prescaler needed
        cmp = ticks;
    } else {
        // Find smallest suitable prescaler
        for (int i = 1; i < APBTIMER_PRESCALER_MAX; i++) {
            if (ticks / (i+1) <= UINT32_MAX) {
                prescaler = i;
                cmp = ticks / (i+1);
                break;
            }
        }
        // Fall through: set everything to max because this is a large timeout.
        if (prescaler == 0) {
            prescaler = APBTIMER_PRESCALER_MAX;
            cmp = UINT32_MAX;
        }
    }
    apbtimer_timeout_conf_t ret = {
        .cmp = cmp,
        .prescaler = prescaler
    };
    return ret;
}

/**
 * Set the prescaler for the timeout timer.
 */
static inline void set_timeout_prescaler(short prescaler) {
    assert(prescaler <= APBTIMER_PRESCALER_MAX);
    // Clear bits in mask
    uint32_t ctrl = regs[TIMER_TIMEOUT]->ctrl &
        (~(APBTIMER_CTRL_PRESCALER_MASK << APBTIMER_CTRL_PRESCALER_SHIFT));
    short prescaler_masked = (prescaler & APBTIMER_CTRL_PRESCALER_MASK)
        << APBTIMER_CTRL_PRESCALER_SHIFT;
    regs[TIMER_TIMEOUT]->ctrl = ctrl | prescaler_masked;
}

/**
 * Set up timekeeper timer for timestamping execution.
 * Use maximum prescaler, disable cmp interrupts to minimise performance
 * impact from timeouts.
 */
static inline void setup_timekeeper(void)
{
    uint8_t prescaler = (0xff & APBTIMER_CTRL_PRESCALER_MASK) <<
        APBTIMER_CTRL_PRESCALER_SHIFT;
    regs[TIMER_TIMEKEEPER]->ctrl = prescaler | APBTIMER_CTRL_EN_BIT;
}

/**
 * Set up the timeout timer for interrupting PDs. Use maximum prescaler initially, don't enable.
 */
static inline void setup_timeouts(void)
{
    uint8_t prescaler = (0xff & APBTIMER_CTRL_PRESCALER_MASK) <<
        APBTIMER_CTRL_PRESCALER_SHIFT;
    regs[TIMER_TIMEKEEPER]->ctrl = prescaler;
}

/**
 * Enable or disable timeout timer.
 */
static inline void timeout_set_enable(bool enable) {
    if (enable) regs[TIMER_TIMEOUT]->ctrl |= APBTIMER_CTRL_EN_BIT;
    else regs[TIMER_TIMEOUT]->ctrl ^= APBTIMER_CTRL_EN_BIT;
}

/**
 * Process timeouts from the queue using the timeout timer.
 * This *differs* from most other sDDF timers because we process timeouts
 * on a relative basis rather than with respect to the absolute time, as such
 * a method is cumbersome and inefficient with 32 bit timers.
 *
 * Timeouts are stored using absolute time upon PPC, this function converts the
 * next timeout into a relative stamp from the current time and awaits it using
 * the timeout timer. Automatically sets prescalar to satisfy most granular time
 * resolution.
 */
static void process_timeouts(void)
{
    uint64_t curr_time = get_time_ns();

    // Pop from priority heap until all timeouts are serviced
    while (timer_heap_peek(*timeouts) != NULL && timer_heap_peek(*timeouts).timestamp <= curr_time) {
        timeout_t expired;
        bool ret = timer_heap_pop(*timeouts, &expired);
        assert(ret);    // This should never happen! Peek should catch empty queue
        microkit_notify(expired.client_channel);
    }

    timeout_t next = timer_heap_peek(*timeouts);
    // Reissue next timeout irq, if needed.
    if (next != NULL) {
        uint64_t next_delay = next.timestamp - curr_time;
        apbtimer_timeout_conf_t next_conf = calculate_timeout_from_ns(next_delay);
        set_timeout_prescaler(next_conf.prescaler);
        regs[TIMER_TIMEOUT]->cmp = next_conf.cmp;
        // Start timeout timer running
        timeout_set_enable(true);
    }
}

void notified(microkit_channel ch)
{
    if (ch == timekeeper_irq) {
        timekeeper_overflow_count += 1;
    } else if (ch == timeout_irq) {
        timeout_set_enable(true);
        process_timeouts();
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
        uint64_t time_ns = get_time_ns();
        seL4_SetMR(0, time_ns);
        return microkit_msginfo_new(0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = get_time_ns();
        uint64_t offset_ns = seL4_GetMR(0);
        timeouts[ch - CLIENT_CH_START] = curr_time + offset_ns;
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

void init(void)
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    timekeeper_irq = device_resources.irqs[TIMER_TIMEKEEPER].id;
    timeout_irq = device_resources.irqs[TIMER_TIMEOUT].id;

    uintptr_t timer_base = (uintptr_t)device_resources.regions[0].region.vaddr;
    regs = (timer_regs**) timer_base;

    setup_timekeeper();
    setup_timeouts();

    // Initialise priority heap
    timer_heap_init(*timeouts);
}
