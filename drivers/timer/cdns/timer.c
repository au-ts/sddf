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
 * the 100MHz clock in the low power domain (LPD).
 * First timer: always on, keeps track of system running time.
 * Second timer: used for timing timeouts. Currently supports a maximum of ~42s timeout.
 */
// TODO: setup to use 2 timers
// 100 MHz frequency in LPD (low power domain clock), later need to read/set up specifc freq: https://github.com/seL4/util_libs/blob/9b8ea7dcf1d80b80b8b7a2a038e03ac10308f39b/libplatsupport/src/mach/zynq/timer.c#L135
#define ZCU102_TIMER_TICKS_PER_SECOND 0x5F5E100

#define TTC_COUNTER_TIMER 0
#define TTC_TIMEOUT_TIMER 1
#define ZCU102_TIMER_MAX_TICKS UINT32_MAX
#define ZCU102_TIMER_CTL_RESET 0x21
#define ZCU102_TIMER_DISABLE 0x1
#define ZCU102_TIMER_CNT_RESET BIT(4)
// Counter control values
#define ZCU102_TIMER_ENABLE_INTERVAL_MODE BIT(1)
#define ZCU102_TIMER_ENABLE_DECREMENT_MODE BIT(2)
#define ZCU102_TIMER_ENABLE_MATCH_MODE BIT(3)
// interrupt enable values
// 0 -> interval, 1 -> match 1, 2 -> match 2, 3 -> match 3, 4 -> counter overflow, 5 -> event_overflow(notused)
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
    uint32_t clk_ctrl[3];       /* 0x00: clock control registers */
    uint32_t cnt_ctrl[3];       /* 0x0C: counter control registers: Operational mode and reset */
    uint32_t cnt_val[3];        /* 0x18: current counter values */
    uint32_t interval_val[3];   /* 0x24: interval value (from which/to which the counter counts) */
    uint32_t match_1[3];        /* 0x30: 1st match values */
    uint32_t match_2[3];        /* 0x3C: 2nd match values */
    uint32_t match_3[3];        /* 0x48: 3rd match values */
    uint32_t int_sts[3];        /* 0x54: status for interval, match, overflow and event interrupts */
    uint32_t int_en[3];         /* 0x60: enable interrupts */
    uint32_t event_ctrl[3];     /* 0x6C: (not used) enable event timer, stop timer */
    uint32_t event[3];          /* 0x78: (not used) width of external pulse */
} zcu102_timer_regs_t;


/* Keeps track of how many counter timer overflows happens,
 * as the counter is 32-bit. This is used as high bits of
 * a 64-bit counter.
 */
uint32_t counter_timer_elapses = 0;
volatile zcu102_timer_regs_t *timer_regs;
microkit_channel counter_irq;
microkit_channel timeout_irq;

#define CLIENT_CH_START 2
#define MAX_TIMEOUTS 6
static uint64_t timeouts[MAX_TIMEOUTS];

static inline uint64_t get_ticks_in_ns(void)
{
    uint64_t value_h = (uint64_t) counter_timer_elapses;
    uint64_t value_l = (uint64_t) timer_regs->cnt_val[TTC_COUNTER_TIMER];

    /* Include unhandled interrupt in value_h */
    // XXX: check if not race condition -> does reading (and therefore clearing) the interrupt register cancel the interrupt from being handled? Will counter_timer_elapses be incremented immediately after?
    if (timer_regs->int_sts[TTC_COUNTER_TIMER] & ZCU102_TIMER_ENABLE_OVERFLOW_INTERRUPT) {
        ++value_h;
        ++counter_timer_elapses;
        sddf_printf("RACE CONDITION: get_ticks_in_ns incrementing counter_timer_elapses\n");
    }
    // TODO: include unhandled IRQ? here or in notified
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
    // as we are using a 32-bit timer, timeouts are done using a MATCH register,
    // but with a check if we havent overflowed
    /* stop the timeout timer */
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_DISABLE;
    uint64_t ticks_whole_seconds = (ns / NS_IN_S) * ZCU102_TIMER_TICKS_PER_SECOND;
    uint64_t ticks_remainder = (ns % NS_IN_S) * ZCU102_TIMER_TICKS_PER_SECOND / NS_IN_S;
    uint64_t num_ticks = ticks_whole_seconds + ticks_remainder;

    assert(num_ticks <= ZCU102_TIMER_MAX_TICKS);
    if (num_ticks > ZCU102_TIMER_MAX_TICKS) {
        sddf_dprintf("ERROR: num_ticks: 0x%lx\n", num_ticks);
    }
    timer_regs->interval_val[TTC_TIMEOUT_TIMER] = (uint32_t) num_ticks;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |=  ZCU102_TIMER_CNT_RESET;
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
        sddf_printf("Setting timeout! ns: %lu\n", ns);
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

    timer_regs = (zcu102_timer_regs_t*) device_resources.regions[0].region.vaddr;
    counter_irq = device_resources.irqs[TTC_COUNTER_TIMER].id;
    timeout_irq = device_resources.irqs[TTC_TIMEOUT_TIMER].id;

    uint32_t ctrl = timer_regs->clk_ctrl[TTC_COUNTER_TIMER];
    /* 0th bit set to 1 -> timer counter stopped */
    if (ctrl & 0x1) {
        sddf_dprintf("timer counter is not started\n");
    } else {
        sddf_dprintf("timer counter is started\n");
    }
    sddf_dprintf("REG_COUNTER_CTL is: 0x%x\n", timer_regs->cnt_ctrl[TTC_COUNTER_TIMER]);

    // Table 14-9
    /* stop timers */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] = ctrl | BIT(0);
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] = ctrl | BIT(0);
    ctrl = ZCU102_TIMER_CTL_RESET;
    /* Reset counter control registers */
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] = ctrl;
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
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] = ctrl | ZCU102_TIMER_CNT_RESET;
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] = ctrl | ZCU102_TIMER_CNT_RESET;


    /* Setup 0th timer as overflow timer */
    timer_regs->int_en[TTC_COUNTER_TIMER] = ZCU102_TIMER_ENABLE_OVERFLOW_INTERRUPT;

    /* Setup 1st timer as timeout timer */
    timer_regs->int_en[TTC_TIMEOUT_TIMER] = ZCU102_TIMER_ENABLE_INTERVAL_INTERRUPT; 
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_ENABLE_INTERVAL_MODE;
    //TODO: test decrement mode
    //timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_ENABLE_DECREMENT_MODE;

    // MATCH MODE
    //// enable match mode
    //sddf_dprintf("ctrl : 0x%x\n", ctrl);
    //ctrl = ctrl | BIT(3);
    //sddf_dprintf("after ctrl : 0x%x\n", ctrl);
    //// enable match interrupt
    //// COUNTER_IER values
    //// 0 -> interval, 1 -> match 1, 2 -> match 2, 3 -> match 3, 4 -> counter overflow, 5 -> event_overflow(notused)
    //*REG_PTR(REG_COUNTER_IER) = BIT(3);
    //*REG_PTR(REG_COUNTER_CTL) = ctrl;
    //// Match after 3 s
    //*REG_PTR(REG_COUNTER_MATCH1) = 1*(uint32_t) ZCU102_TIMER_TICKS_PER_SECOND;
    //*REG_PTR(REG_COUNTER_MATCH2) = 5*(uint32_t) ZCU102_TIMER_TICKS_PER_SECOND;
    //*REG_PTR(REG_COUNTER_MATCH3) = 30*(uint32_t) ZCU102_TIMER_TICKS_PER_SECOND;
    //sddf_dprintf("interrupt enable: 0x%x\n", *REG_PTR(REG_COUNTER_IER));
    //sddf_dprintf("match reg: 0x%x match2: 0x%x\n", *REG_PTR(REG_COUNTER_MATCH1), *REG_PTR(REG_COUNTER_MATCH2));
    // XXX WIP: atm does not match, but does issue IRQ every ~42 seconds (2**32 / ZCU102_TIMER_TICKS_PER_SECOND)

    // ===== INTERVAL MODE ====
    //// Set up interval value
    //// enable interval interrupt
    ////timer_regs->int_en[TTC_COUNTER_TIMER] = ZCU102_TIMER_ENABLE_INTERVAL_INTERRUPT;
    //// 0 -> interval, 1 -> match 1, 2 -> match 2, 3 -> match 3, 4 -> counter overflow, 5 -> event_overflow(notused)
    //timer_regs->int_en[TTC_COUNTER_TIMER] = BIT(4);
    //// clock 100MHz ? below will tick every second
    ////timer_regs->interval_val[TTC_COUNTER_TIMER] =  0x5F5E100;
    ////timer_regs->match_3[TTC_COUNTER_TIMER] = ZCU102_TIMER_TICKS_PER_SECOND;

    ////ctrl = ctrl | ZCU102_TIMER_ENABLE_INTERVAL_MODE;
    //ctrl = ctrl | ZCU102_TIMER_ENABLE_MATCH_MODE;

    //// Enable interval mode
    // ===== INTERVAL MODE ====

    //Start the counter
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] = ctrl ^ ZCU102_TIMER_DISABLE;
    sddf_dprintf("start counter: 0x%x\n", ctrl ^ ZCU102_TIMER_DISABLE);
    sddf_dprintf("REG_COUNTER_CTL is: 0x%x\n", timer_regs->cnt_ctrl[TTC_COUNTER_TIMER]);

    for (int i = 0; i < 100; i++) {
        sddf_dprintf("i %d, value: 0x%x\n", i, timer_regs->cnt_val[TTC_COUNTER_TIMER]);
    }
}

void notified(microkit_channel ch)
{
    sddf_printf("interrupt on channel %d\n", ch);
    assert(ch == counter_irq || ch == timeout_irq);
    if (ch == counter_irq) {
        sddf_dprintf("Overflow! Interrupt received!\n");
        sddf_printf("Timeout counter val: %u, interrupt val: %u\n", timer_regs->cnt_val[TTC_TIMEOUT_TIMER], timer_regs->interval_val[TTC_TIMEOUT_TIMER]);
        /* Overflow on timekeeping counter */
        if (timer_regs->int_sts[TTC_COUNTER_TIMER] & ZCU102_TIMER_ENABLE_OVERFLOW_INTERRUPT) {
            ++counter_timer_elapses;
        } else {
            /* race condition: get_ticks_in_ns() was called from timeout_irq handling, and overflow timer issued irq during handling,
             * counter_timer_elapses already incremented
             */
            sddf_printf("RACE CONDITION: already incremented counter_timer_elapses\n");
        }

        /* interrupt cleared on read by device */
        // XXX: maybe spin on this?
        uint32_t int_sts = timer_regs->int_sts[TTC_COUNTER_TIMER];
        sddf_printf("int_sts: 0x%x\n", int_sts);
    } else if (ch == timeout_irq) {
        /* Timeout counter reached 0 */
        // XXX: later: allow timeouts greater than UINT32_MAX ticks
        /* stop the timeout timer */
        sddf_printf("timeout! interrupt received!\n");
        timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] |= ZCU102_TIMER_DISABLE;
        uint64_t curr_time = get_ticks_in_ns();
        process_timeouts(curr_time);
        uint32_t int_sts = timer_regs->int_sts[TTC_TIMEOUT_TIMER];
        sddf_printf("int_sts: 0x%x\n", int_sts);
        assert(int_sts == ZCU102_TIMER_ENABLE_INTERVAL_INTERRUPT);
    } else {
        /* Unknown channel, panic! */
        sddf_dprintf("ERROR: timer notified on unknown channel: %d\n", ch);
        // XXX: for now, crash. later handle better
        __builtin_trap();
    }

    //sddf_dprintf("Interrupt reg: 0x%x\n", timer_regs->int_sts[TTC_COUNTER_TIMER]);
    //sddf_dprintf("Interrupt reg: 0x%x\n", timer_regs->int_sts[TTC_COUNTER_TIMER]);
    //sddf_dprintf("counter val: 0x%x\n", timer_regs->cnt_val[TTC_COUNTER_TIMER]);
    //sddf_printf("reset counter\n");
    //timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] |= BIT(4);

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
        sddf_printf("Curr time %lu, timeout %lu\n", curr_time, timeouts[ch]);
        process_timeouts(curr_time);
        break;
    }
    default:
        sddf_dprintf("TIMER DRIVER|LOG: Unknown request %lu to timer from channel %u\n", microkit_msginfo_get_label(msginfo),
                     ch);
        break;
    }

    return microkit_msginfo_new(0, 0);
}
