/*
 * Copyright 2024, UNSW
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

/*
 * Zynq UltraScale+ MPSoC contains a timer (Cadence Triple Timer Clock) with 3 32-bit counters.
 * Only 2 of the 3 timers are used in this driver. All 3 timers by default are connected to
 * the LSBUS clock in the Low Power Domain, (controlled by LPD_LSBUS_CTRL).
 */
/* TODO:
 * More graceful error when user requests timeout greater than served by ZCU102_TIMER_MAX_TICKS (at 25MHz (downscaled), 32-bit counter thats ~2min 51.799s)
 * Allow timeouts greater than UINT32_MAX ticks
 */

#define ZCU102_TIMER_MAX_PRESCALE 0xf
/* prescale: rate = clk_src/[2^(N+1)] */
#define ZCU102_TIMER_PRESCALE_VALUE 0x1
#if defined(CONFIG_PLAT_ZYNQMP)
/*
 * By default, the LSBUS clock is using IOPLL clock as source, and divides down by 15 to 100MHz.
 * See: https://docs.amd.com/r/en-US/ug1087-zynq-ultrascale-registers/LPD_LSBUS_CTRL-CRL_APB-Register.
 * You can read the IOPLL clk value in u-boot using `clk dump` and view the source and divider value for
 * LSBUS by reading LPD_LSBUS_CTRL register.
*/
#define ZCU102_TIMER_REF_CLOCK_RATE (100UL * 1000UL * 1000UL)
#else
#error "unknown LSBUS clock frequency (timer device reference clock)"
#endif
/* default source clock, scaled down by a factor of 2^(ZCU102_TIMER_PRESCALE_VALUE+1) */
#define ZCU102_TIMER_TICKS_PER_SECOND (ZCU102_TIMER_REF_CLOCK_RATE >> ((ZCU102_TIMER_PRESCALE_VALUE & ZCU102_TIMER_MAX_PRESCALE) + 1))

#define TTC_COUNTER_TIMER 0
#define TTC_TIMEOUT_TIMER 1
#define ZCU102_TIMER_MAX_TICKS UINT32_MAX
#define ZCU102_TIMER_CTL_RESET 0x21
#define ZCU102_TIMER_DISABLE 0x1
#define ZCU102_TIMER_CNT_RESET BIT(4)
/* Clock control values */
#define ZCU102_TIMER_ENABLE_PRESCALE BIT(0)
/* Counter control values */
#define ZCU102_TIMER_ENABLE_INTERVAL_MODE BIT(1)
#define ZCU102_TIMER_ENABLE_DECREMENT_MODE BIT(2)
#define ZCU102_TIMER_ENABLE_MATCH_MODE BIT(3)
/* interrupt enable values */
#define ZCU102_TIMER_ENABLE_INTERVAL_INTERRUPT BIT(0)
#define ZCU102_TIMER_ENABLE_MATCH1_INTERRUPT BIT(1)
#define ZCU102_TIMER_ENABLE_MATCH2_INTERRUPT BIT(2)
#define ZCU102_TIMER_ENABLE_MATCH3_INTERRUPT BIT(3)
#define ZCU102_TIMER_ENABLE_OVERFLOW_INTERRUPT BIT(4)
#define ZCU102_TIMER_ENABLE_EVNT_OVERFLOW_INTERRUPT BIT(5)

typedef struct {
    /* Registers (for each of the 3 counters in the Triple Timer Clock)
     * NOTE: 0th timer is used as a general time counter, 1st timer is used as a timeout timer.
     * Last timer is unused. */
    uint32_t clk_ctrl[3];     /* 0x00: clock control registers */
    uint32_t cnt_ctrl[3];     /* 0x0C: counter control registers: Operational mode and reset */
    uint32_t cnt_val[3];      /* 0x18: current counter values */
    uint32_t interval_val[3]; /* 0x24: interval value (from which/to which the counter counts) */
    uint32_t match_1[3];      /* 0x30: 1st match values */
    uint32_t match_2[3];      /* 0x3C: 2nd match values */
    uint32_t match_3[3];      /* 0x48: 3rd match values */
    uint32_t int_sts[3];      /* 0x54: status for interval, match, overflow and event interrupts */
    uint32_t int_en[3];       /* 0x60: enable interrupts */
    uint32_t event_ctrl[3];   /* 0x6C: (not used) enable event timer, stop timer */
    uint32_t event[3];        /* 0x78: (not used) width of external pulse */
} zcu102_timer_regs_t;

/* Keeps track of how many counter timer overflows happens,
 * as the counter is 32-bit. This is used as high bits of
 * a 64-bit counter.
 */
uint32_t counter_timer_elapses = 0;
volatile zcu102_timer_regs_t *timer_regs;
microkit_channel counter_irq;
microkit_channel timeout_irq;

/* offset for the 2 interrupt channels */
#define CLIENT_CH_START 2
#define MAX_TIMEOUTS 6
static uint64_t timeouts[MAX_TIMEOUTS];

static inline uint64_t get_ticks_in_ns(void)
{
    uint64_t value_h = (uint64_t)counter_timer_elapses;
    uint64_t value_l = (uint64_t)timer_regs->cnt_val[TTC_COUNTER_TIMER];

    /* Include unhandled interrupt in value_h */
    if (timer_regs->int_sts[TTC_COUNTER_TIMER] & ZCU102_TIMER_ENABLE_OVERFLOW_INTERRUPT) {
        ++value_h;
        value_l = (uint64_t)timer_regs->cnt_val[TTC_COUNTER_TIMER];
        /*
         * XXX: Weird behaviour: If overflow IRQ happens here (while handling TIMEOUT IRQ), and the IRQ status register for
         * TTC_COUNTER_TIMER (the overflow one) gets read (cleared), sometimes the IRQ for overflow
         * gets delivered (notified() called), but sometimes not. Current solution is to increment the global counter_timer_elapses
         * in this function, and if during handling overflow IRQ the IRQ status register is cleared, do not increment.
         */
        ++counter_timer_elapses;
    }
    uint64_t value_ticks = (value_h << 32) | value_l;

    /* convert from ticks to nanoseconds */
    uint64_t value_whole_seconds = value_ticks / ZCU102_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ticks = value_ticks % ZCU102_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ns = (value_subsecond_ticks * NS_IN_S) / ZCU102_TIMER_TICKS_PER_SECOND;
    uint64_t value_ns = value_whole_seconds * NS_IN_S + value_subsecond_ns;

    return value_ns;
}

void set_timeout(uint64_t ns)
{
    /* stop the timeout timer */
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_DISABLE;
    uint64_t ticks_whole_seconds = (ns / NS_IN_S) * ZCU102_TIMER_TICKS_PER_SECOND;
    uint64_t ticks_remainder = (ns % NS_IN_S) * ZCU102_TIMER_TICKS_PER_SECOND / NS_IN_S;
    uint64_t num_ticks = ticks_whole_seconds + ticks_remainder;

    assert(num_ticks <= ZCU102_TIMER_MAX_TICKS);
    if (num_ticks > ZCU102_TIMER_MAX_TICKS) {
        sddf_dprintf("ERROR: requested timeout num_ticks: 0x%lx exceeds counter resolution: 0x%x\n", num_ticks,
                     ZCU102_TIMER_MAX_TICKS);
    }
    timer_regs->interval_val[TTC_TIMEOUT_TIMER] = (uint32_t)num_ticks;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_CNT_RESET;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] ^= ZCU102_TIMER_DISABLE;
}

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            microkit_notify(CLIENT_CH_START + i);
            timeouts[i] = UINT64_MAX;
        }
    }

    uint64_t next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] < next_timeout) {
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
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    timer_regs = (zcu102_timer_regs_t *)device_resources.regions[0].region.vaddr;
    counter_irq = device_resources.irqs[TTC_COUNTER_TIMER].id;
    timeout_irq = device_resources.irqs[TTC_TIMEOUT_TIMER].id;

    /* Table 14-9 */
    /* stop timers */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] |= ZCU102_TIMER_DISABLE;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_DISABLE;
    /* Reset counter control registers */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] = ZCU102_TIMER_CTL_RESET;
    timer_regs->clk_ctrl[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->interval_val[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->match_1[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->match_2[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->match_3[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->int_en[TTC_COUNTER_TIMER] = 0x0;
    timer_regs->int_sts[TTC_COUNTER_TIMER] = 0x0;

    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] = ZCU102_TIMER_CTL_RESET;
    timer_regs->clk_ctrl[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->interval_val[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->match_1[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->match_2[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->match_3[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->int_en[TTC_TIMEOUT_TIMER] = 0x0;
    timer_regs->int_sts[TTC_TIMEOUT_TIMER] = 0x0;
    /* Reset counters */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] |= ZCU102_TIMER_CNT_RESET;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_CNT_RESET;

    /* Setup 0th timer as overflow timer */
    timer_regs->int_en[TTC_COUNTER_TIMER] = ZCU102_TIMER_ENABLE_OVERFLOW_INTERRUPT;

    /* Setup 1st timer as timeout timer, using interval mode */
    timer_regs->int_en[TTC_TIMEOUT_TIMER] = ZCU102_TIMER_ENABLE_INTERVAL_INTERRUPT;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_ENABLE_INTERVAL_MODE;

    /* Set up prescaler, divide down from 100MHz to ZCU102_TIMER_TICKS_PER_SECOND */
    timer_regs->clk_ctrl[TTC_COUNTER_TIMER] = ((ZCU102_TIMER_PRESCALE_VALUE & ZCU102_TIMER_MAX_PRESCALE) << 1)
                                            | ZCU102_TIMER_ENABLE_PRESCALE;
    timer_regs->clk_ctrl[TTC_TIMEOUT_TIMER] = ((ZCU102_TIMER_PRESCALE_VALUE & ZCU102_TIMER_MAX_PRESCALE) << 1)
                                            | ZCU102_TIMER_ENABLE_PRESCALE;

    /* Start the TTC_COUNTER_TIMER */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] ^= ZCU102_TIMER_DISABLE;
}

void notified(microkit_channel ch)
{
    assert(ch == counter_irq || ch == timeout_irq);
    if (ch == counter_irq) {
        /* Overflow on timekeeping counter, interrupt cleared on read by device */
        if (timer_regs->int_sts[TTC_COUNTER_TIMER] & ZCU102_TIMER_ENABLE_OVERFLOW_INTERRUPT) {
            ++counter_timer_elapses;
        } else {
            /*
             * race condition: get_ticks_in_ns() was called from timeout_irq handling, and overflow timer
             * issued irq during handling, counter_timer_elapses already incremented
             */
        }
    } else if (ch == timeout_irq) {
        /* Timeout counter reached 0, stop the timeout timer */
        timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_DISABLE;
        uint64_t curr_time = get_ticks_in_ns();
        process_timeouts(curr_time);
        /* interrupt cleared on read by device */
        uint32_t int_sts = timer_regs->int_sts[TTC_TIMEOUT_TIMER];
        assert(int_sts == ZCU102_TIMER_ENABLE_INTERVAL_INTERRUPT);
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
        uint64_t time_ns = get_ticks_in_ns();
        seL4_SetMR(0, time_ns);
        return microkit_msginfo_new(0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = get_ticks_in_ns();
        uint64_t offset_us = (uint64_t)(seL4_GetMR(0));
        timeouts[ch - CLIENT_CH_START] = curr_time + offset_us;
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
