/*
 * Copyright 2024, UNSW
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

/*
 * Zynq UltraScale+ MPSoC contains a timer (Cadence Triple Timer Clock) with 3 32-bit counters.
 * Only 2 of the 3 timers are used in this driver. All 3 timers by default are connected to
 * the LSBUS clock in the Low Power Domain, (controlled by LPD_LSBUS_CTRL).
 */

#define CDNS_TIMER_MAX_PRESCALE 0xf
/* prescale: rate = clk_src/[2^(N+1)] */
#define CDNS_TIMER_PRESCALE_VALUE 0x1
#if defined(CONFIG_PLAT_ZYNQMP)
/*
 * By default, the LSBUS clock is using IOPLL clock as source, and divides down by 15 to 100MHz.
 * See: https://docs.amd.com/r/en-US/ug1087-zynq-ultrascale-registers/LPD_LSBUS_CTRL-CRL_APB-Register.
 * You can read the IOPLL clk value in u-boot using `clk dump` and view the source and divider value for
 * LSBUS by reading LPD_LSBUS_CTRL register.
*/
#define CDNS_TIMER_REF_CLOCK_RATE (100*MEGA)
#else
#error "unknown LSBUS clock frequency (timer device reference clock)"
#endif
/* default source clock, scaled down by a factor of 2^(CDNS_TIMER_PRESCALE_VALUE+1) if enabled prescale */
#define CDNS_TIMER_TICKS_PER_SECOND (CDNS_TIMER_REF_CLOCK_RATE >> ((CDNS_TIMER_PRESCALE_VALUE & CDNS_TIMER_MAX_PRESCALE) + 1))
#define CDNS_TRUE_PRESCALE (CDNS_TIMER_PRESCALE_VALUE + 1)

#define TTC_COUNTER_TIMER 0
#define TTC_TIMEOUT_TIMER 1

#define TTC_NUM_TIMERS 3

#define CDNS_TIMER_MAX_TICKS UINT32_MAX
#define CDNS_TIMER_CTL_RESET 0x21
#define CDNS_TIMER_DISABLE 0x1
#define CDNS_TIMER_CNT_RESET BIT(4)
/* Clock control values */
#define CDNS_TIMER_ENABLE_PRESCALE BIT(0)
/* Counter control values */
#define CDNS_TIMER_ENABLE_INTERVAL_MODE BIT(1)
#define CDNS_TIMER_ENABLE_DECREMENT_MODE BIT(2)
#define CDNS_TIMER_ENABLE_MATCH_MODE BIT(3)
/* interrupt enable values */
#define CDNS_TIMER_ENABLE_INTERVAL_INTERRUPT BIT(0)
#define CDNS_TIMER_ENABLE_MATCH1_INTERRUPT BIT(1)
#define CDNS_TIMER_ENABLE_MATCH2_INTERRUPT BIT(2)
#define CDNS_TIMER_ENABLE_MATCH3_INTERRUPT BIT(3)
#define CDNS_TIMER_ENABLE_OVERFLOW_INTERRUPT BIT(4)
#define CDNS_TIMER_ENABLE_EVNT_OVERFLOW_INTERRUPT BIT(5)

typedef struct {
    /* Registers (for each of the 3 counters in the Triple Timer Clock)
     * NOTE: 0th timer is used as a general time counter, 1st timer is used as a timeout timer.
     * Last timer is unused. */
    uint32_t clk_ctrl[TTC_NUM_TIMERS];     /* 0x00: clock control registers */
    uint32_t cnt_ctrl[TTC_NUM_TIMERS];     /* 0x0C: counter control registers: Operational mode and reset */
    uint32_t cnt_val[TTC_NUM_TIMERS];      /* 0x18: current counter values */
    uint32_t interval_val[TTC_NUM_TIMERS]; /* 0x24: interval value (from which/to which the counter counts) */
    uint32_t match_1[TTC_NUM_TIMERS];      /* 0x30: 1st match values */
    uint32_t match_2[TTC_NUM_TIMERS];      /* 0x3C: 2nd match values */
    uint32_t match_3[TTC_NUM_TIMERS];      /* 0x48: 3rd match values */
    uint32_t int_sts[TTC_NUM_TIMERS];      /* 0x54: status for interval, match, overflow and event interrupts */
    uint32_t int_en[TTC_NUM_TIMERS];       /* 0x60: enable interrupts */
    uint32_t event_ctrl[TTC_NUM_TIMERS];   /* 0x6C: (not used) enable event timer, stop timer */
    uint32_t event[TTC_NUM_TIMERS];        /* 0x78: (not used) width of external pulse */
} cdns_timer_regs_t;

/* Keeps track of how many counter timer overflows happens,
 * as the counter is 32-bit. This is used as high bits of
 * a 64-bit counter.
 */
uint32_t counter_timer_elapses = 0;
volatile cdns_timer_regs_t *timer_regs;
sddf_channel counter_irq;
sddf_channel timeout_irq;

/* offset for the 2 interrupt channels */
#define CLIENT_CH_START 2
#define MAX_TIMEOUTS SDDF_TIMER_MAX_CLIENTS
static uint64_t target_timeout = UINT64_MAX;

static inline uint64_t get_ticks_in_ns(void)
{
    uint64_t value_h = (uint64_t)counter_timer_elapses;
    uint64_t value_l = (uint64_t)timer_regs->cnt_val[TTC_COUNTER_TIMER];

    /* Include unhandled interrupt in value_h */
    if (timer_regs->int_sts[TTC_COUNTER_TIMER] & CDNS_TIMER_ENABLE_OVERFLOW_INTERRUPT) {
        value_h++;
        value_l = (uint64_t)timer_regs->cnt_val[TTC_COUNTER_TIMER];
        /*
         * XXX: Weird behaviour: If overflow IRQ happens here (while handling TIMEOUT IRQ), and the IRQ status register for
         * TTC_COUNTER_TIMER (the overflow one) gets read (cleared), sometimes the IRQ for overflow
         * gets delivered (notified() called), but sometimes not. Current solution is to increment the global counter_timer_elapses
         * in this function, and if during handling overflow IRQ the IRQ status register is cleared, do not increment.
         */
        counter_timer_elapses++;
    }
    uint64_t value_ticks = (value_h << 32) | value_l;

    /* convert from ticks to nanoseconds */
    return tick_to_ns_cached(value_ticks, CDNS_TRUE_PRESCALE, CDNS_TIMER_REF_CLOCK_RATE);
}

void set_timeout(uint64_t ns)
{
    /* stop the timeout timer */
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= CDNS_TIMER_DISABLE;
    uint64_t num_ticks = ns_to_tick_cached(ns, CDNS_TRUE_PRESCALE, CDNS_TIMER_REF_CLOCK_RATE);

    if (num_ticks > CDNS_TIMER_MAX_TICKS) {
        /* truncate num_ticks to maximum timeout, will use multiple interrupts to process the requested timeout. */
        num_ticks = CDNS_TIMER_MAX_TICKS;
    }
    timer_regs->interval_val[TTC_TIMEOUT_TIMER] = (uint32_t)num_ticks;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= CDNS_TIMER_CNT_RESET;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] ^= CDNS_TIMER_DISABLE;
}

static void process_target_timeout(uint64_t curr_time_ns)
{
    if (target_timeout <= curr_time_ns) {
        sddf_notify(config.virt_id);
        // Update "current" time page with virt
        set_shared_time_page(get_current_time());
        target_timeout = UINT64_MAX;
    }

    if (target_timeout != UINT64_MAX) {
        uint64_t ns = target_timeout - curr_time_ns;
        set_timeout(ns);
    }
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    timer_regs = (cdns_timer_regs_t *)device_resources.regions[0].region.vaddr;
    counter_irq = device_resources.irqs[TTC_COUNTER_TIMER].id;
    timeout_irq = device_resources.irqs[TTC_TIMEOUT_TIMER].id;

    /* Table 14-9 */
    /* stop timers */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] |= CDNS_TIMER_DISABLE;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= CDNS_TIMER_DISABLE;
    /* Reset counter control registers */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] = CDNS_TIMER_CTL_RESET;
    timer_regs->clk_ctrl[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->interval_val[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->match_1[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->match_2[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->match_3[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->int_en[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->int_sts[TTC_COUNTER_TIMER] = 0x0;

    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] = CDNS_TIMER_CTL_RESET;
    timer_regs->clk_ctrl[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->interval_val[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->match_1[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->match_2[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->match_3[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->int_en[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->int_sts[TTC_TIMEOUT_TIMER] = 0x0;
    /* Reset counters */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] |= CDNS_TIMER_CNT_RESET;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= CDNS_TIMER_CNT_RESET;

    /* Setup 0th timer as overflow timer */
    timer_regs->int_en[TTC_COUNTER_TIMER] = CDNS_TIMER_ENABLE_OVERFLOW_INTERRUPT;

    /* Setup 1st timer as timeout timer, using interval mode */
    timer_regs->int_en[TTC_TIMEOUT_TIMER] = CDNS_TIMER_ENABLE_INTERVAL_INTERRUPT;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= CDNS_TIMER_ENABLE_INTERVAL_MODE;

    /* Set up prescaler, divide down from 100MHz to CDNS_TIMER_TICKS_PER_SECOND */
    timer_regs->clk_ctrl[TTC_COUNTER_TIMER] = ((CDNS_TIMER_PRESCALE_VALUE & CDNS_TIMER_MAX_PRESCALE) << 1)
                                            | CDNS_TIMER_ENABLE_PRESCALE;
    timer_regs->clk_ctrl[TTC_TIMEOUT_TIMER] = ((CDNS_TIMER_PRESCALE_VALUE & CDNS_TIMER_MAX_PRESCALE) << 1)
                                            | CDNS_TIMER_ENABLE_PRESCALE;

    /* Start the TTC_COUNTER_TIMER */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] ^= CDNS_TIMER_DISABLE;
}

void notified(sddf_channel ch)
{
    assert(ch == counter_irq || ch == timeout_irq);
    if (ch == counter_irq) {
        /* Overflow on timekeeping counter, interrupt cleared on read by device */
        if (timer_regs->int_sts[TTC_COUNTER_TIMER] & CDNS_TIMER_ENABLE_OVERFLOW_INTERRUPT) {
            ++counter_timer_elapses;
        } else {
            /*
             * race condition: get_ticks_in_ns() was called from timeout_irq handling, and overflow timer
             * issued irq during handling, counter_timer_elapses already incremented
             */
        }
    } else if (ch == timeout_irq) {
        /* Timeout counter reached 0, stop the timeout timer */
        timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= CDNS_TIMER_DISABLE;
        uint64_t curr_time = get_ticks_in_ns();
        process_target_timeout(curr_time);
        /* interrupt cleared on read by device */
        uint32_t int_sts = timer_regs->int_sts[TTC_TIMEOUT_TIMER];
        assert(int_sts == CDNS_TIMER_ENABLE_INTERVAL_INTERRUPT);
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
