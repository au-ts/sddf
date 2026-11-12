/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/timer/config.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/resources/device.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/arch_timestamp_counter.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>

// #define DEBUG_APBTIMER

#ifdef DEBUG_APBTIMER
#define LOG_APBTIMER(...) do{ sddf_dprintf("APBTIMER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_APBTIMER(...) do{}while(0)
#endif

#define LOG_APBTIMER_ERR(...) do{ sddf_dprintf("APBTIMER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

#define NUM_TIMERS 2 // Adjust if synthesised with more timers.                                                                       \
                        // Minimum = 2 due to a bug in the HDL, assumed for rest of this driver.
#define APBTIMER_MAX_TICKS (UINT32_MAX)
#define APBTIMER_CLK_FREQ ((uint64_t)50000000) // 50MHz

// The APB timer has an array of internal timers. Use one for long-running time measurements, use
// the other for generating interrupts at finer granularity using prescalers.
// TODO: support >2 timers; probably exposed over a different API for drivers etc?
#define TIMER_TIMEOUT    (0)
// We are conservative with IRQs in config.json. We don't use the 2nd (cmp) interrupt
// for the timekeeper, and since that IRQ isn't in config.json we must make sure the timekeeper
// is the last ID to avoid accessing the wrong IRQ.
#define TIMER_TIMEKEEPER (1)

// NOTE: at the time of writing, the APB timer's prescaler logic is completely
// broken. We use no prescaler as a result.
#define TIMEKEEPER_PRESCALER (0)

#define APBTIMER_CTRL_EN_BIT            (BIT(0))
#define APBTIMER_CTRL_PRESCALER_SHIFT   (3)
#define APBTIMER_CTRL_PRESCALER_MASK    (0b111) // *before* shift - see timer setup functions
#define APBTIMER_PRESCALER_MAX          ((0xff & APBTIMER_CTRL_PRESCALER_MASK))

// Use these defines with the timer ID (timekeeper or timeout)
#define APBTIMER_NUM_IRQ    (2)
#define OVERFLOW_IRQ(n)     (device_resources.irqs[(2*n)].id)
#define CMP_IRQ(n)          (device_resources.irqs[(2*n)+1].id)

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
timer_driver_config_t *config;

// Timer block implements NUM_TIMERS separate timers with back-to-back registers
struct timer_regs {
    uint32_t timer;
    uint32_t ctrl;
    uint32_t cmp;
    uint32_t unused; // Timers are spaced by 16 bytes, last 32 bits are unused
};

// Array of regs structs, not just one set!
volatile struct timer_regs *regs;
static bool armed;

/* Keep track of how many timer overflows have occured.
 * Used as the most significant segment of ticks.
 * We need to keep track of this state as the value register is only
 * 32 bits as opposed to the common 64 bit timer value regsiters found
 * on other devices.
 */
uint32_t timekeeper_overflow_count = 0;

typedef struct apbtimer_timeout_conf {
    uint32_t cmp;
    uint8_t prescaler;
} apbtimer_timeout_conf_t;

/**
 * Return number of ticks since driver startup using timekeeper timer.
 * NOTE: one round of timer @ 50MHz with prescaler of (1<<3)=4 lasts for 171.8
 *          seconds. Time resolution = 80ns per tick.
 */
static uint64_t get_time_ns(void)
{
    uint64_t value_l = (uint64_t)(regs[TIMER_TIMEKEEPER].timer);
    uint64_t value_h = (uint64_t)timekeeper_overflow_count;
    uint64_t value_ticks = (value_h << 32) | value_l;

    return ticks_to_ns_prescaled(value_ticks, TIMEKEEPER_PRESCALER, APBTIMER_CLK_FREQ);
}

/**
 * Calculate the cmp value and prescaler for the timeout timer given
 * a desired delay in nanoseconds. If delay exceeds capacity of timer,
 * returns maximum prescaler and cmp.
 */
static apbtimer_timeout_conf_t calculate_timeout_from_ns(uint64_t ns_delay)
{
    // Convert nanoseconds to ticks with a prescaler of zero (x1)
    uint64_t ticks = ns_to_ticks(ns_delay, APBTIMER_CLK_FREQ);

    uint32_t prescaler = 0;
    uint32_t cmp = ticks;
    // NOTE: at the time of writing, the APB timer's prescaler logic is completely
    // broken. The prescaler calculator is disabled as a result.

    // if (ticks < UINT32_MAX - 1) {
    //     // No prescaler needed
    //     cmp = ticks;
    // } else {
    //     // Find smallest suitable prescaler
    //     for (int i = 1; i < APBTIMER_PRESCALER_MAX; i++) {
    //         if (ticks / (i + 1) <= UINT32_MAX) {
    //             prescaler = i;
    //             cmp = ticks / (i + 1);
    //             break;
    //         }
    //     }
    //     // Fall through: set everything to max because this is a large timeout.
    //     if (prescaler == 0) {
    //         prescaler = APBTIMER_PRESCALER_MAX;
    //         cmp = UINT32_MAX;
    //     }
    // }
    apbtimer_timeout_conf_t ret = { .cmp = cmp, .prescaler = prescaler };
    return ret;
}

/**
 * Set the prescaler for the timeout timer.
 */
static inline void set_timeout_prescaler(uint8_t prescaler)
{
    assert(prescaler <= APBTIMER_PRESCALER_MAX);
    // Clear bits in mask
    uint32_t ctrl = regs[TIMER_TIMEOUT].ctrl & (~(APBTIMER_CTRL_PRESCALER_MASK << APBTIMER_CTRL_PRESCALER_SHIFT));
    uint8_t prescaler_masked = (prescaler & APBTIMER_CTRL_PRESCALER_MASK) << APBTIMER_CTRL_PRESCALER_SHIFT;
    regs[TIMER_TIMEOUT].ctrl = ctrl | prescaler_masked;
    assert(regs[TIMER_TIMEOUT].ctrl == (ctrl | prescaler_masked));
}

/**
 * Set up timekeeper timer for timestamping execution.
 * Use maximum prescaler, disable cmp interrupts to minimise performance
 * impact from timeouts.
 */
static inline void setup_timekeeper(void)
{
    uint8_t prescaler = (TIMEKEEPER_PRESCALER & APBTIMER_CTRL_PRESCALER_MASK) << APBTIMER_CTRL_PRESCALER_SHIFT;
    regs[TIMER_TIMEKEEPER].ctrl = prescaler;
    regs[TIMER_TIMEKEEPER].ctrl |= APBTIMER_CTRL_EN_BIT;
    assert(regs[TIMER_TIMEKEEPER].ctrl == (prescaler | APBTIMER_CTRL_EN_BIT));
}

/**
 * Calculate cmp value for the timeout given a delay in architecture counter ticks.
 * If delay exceeds capacity of timer return maximum cmp.
 */
static uint32_t calculate_timeout_from_arch_ticks(uint64_t tick_delay)
{
    uint64_t freq = sddf_read_freq();
    uint32_t cmp = APBTIMER_MAX_TICKS - 1;
    if (tick_delay <= period_transform(cmp, freq, APBTIMER_CLK_FREQ)) {
        cmp = period_transform(tick_delay, APBTIMER_CLK_FREQ, freq);
    }
    return MAX(cmp, 1);
}
/**
 * Enable or disable timeout timer.
 */
static inline void timeout_set_enable(bool enable)
{
    if (enable) {
        regs[TIMER_TIMEOUT].ctrl |= APBTIMER_CTRL_EN_BIT;
        assert(regs[TIMER_TIMEOUT].ctrl & APBTIMER_CTRL_EN_BIT);
    } else {
        regs[TIMER_TIMEOUT].ctrl &= ~APBTIMER_CTRL_EN_BIT;
        assert(!(regs[TIMER_TIMEOUT].ctrl & APBTIMER_CTRL_EN_BIT));
    }
}

void notified(microkit_channel ch)
{
    LOG_APBTIMER("notified by channel %u\n", ch);
    if (ch == CMP_IRQ(TIMER_TIMEOUT) || ch == OVERFLOW_IRQ(TIMER_TIMEOUT)) {
        LOG_APBTIMER("timeout irq!\n");
        timeout_set_enable(0);
        regs[TIMER_TIMEOUT].timer = 0;
        if (armed) {
            armed = false;
            microkit_notify(config->virt_id);
        }
    }
    microkit_deferred_irq_ack(ch);
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    LOG_APBTIMER("ppc from channel %u\n", ch);
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t next_timeout = seL4_GetMR(0);
        timeout_set_enable(0);
        uint64_t curr_time = sddf_read_counter();
        uint64_t next_delay = next_timeout > curr_time ? next_timeout - curr_time : 0;
        uint64_t cmp = calculate_timeout_from_arch_ticks(next_delay);
        regs[TIMER_TIMEOUT].cmp = cmp;
        armed = true;
        timeout_set_enable(1);
        break;
    }
    default:
        LOG_APBTIMER("Unknown request %lu to timer from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        break;
    }

    return microkit_msginfo_new(0, 0);
}

void init(void)
{
    assert(timer_config_check_magic(config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 4);
    assert(device_resources.num_regions == 1);

    uintptr_t timer_base = (uintptr_t)device_resources.regions[0].region.vaddr;
    regs = (volatile struct timer_regs *)timer_base;

    for (int i = 0; i < NUM_TIMERS; i++) {
        regs[i].ctrl = 0;
        regs[i].timer = 0;
        regs[i].cmp = 0;
    }
    armed = false;
}
