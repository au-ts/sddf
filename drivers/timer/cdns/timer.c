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

// TODO: setup to use 2 timers
// 100 MHz frequency in LPD (low power domain clock), later need to read/set up specifc freq: https://github.com/seL4/util_libs/blob/9b8ea7dcf1d80b80b8b7a2a038e03ac10308f39b/libplatsupport/src/mach/zynq/timer.c#L135
#define ZCU102_TIMER_TICKS_PER_SECOND 0x5F5E100

//volatile void *regs;
//#define REG_PTR(off)     ((volatile uint32_t *)((regs) + (off)))
//
//#define REG_COUNTER_CTL 0x0C
//#define REG_COUNTER_VALUE 0x18
//#define REG_COUNTER_CLK_CTL 0x0
//#define REG_COUNTER_INTERVAL_COUNT 0x24
//#define REG_COUNTER_MATCH1 0x3C
//#define REG_COUNTER_MATCH2 0x48
//#define REG_COUNTER_IER 0x60
//#define REG_COUNTER_ISR 0x54

#define TTC_COUNTER_TIMER 0
#define TTC_TIMEOUT_TIMER 1
#define ZCU102_TIMER_MAX_TICKS UINT32_MAX
#define ZCU102_TIMER_CTL_RESET 0x21
// Counter control values
#define ZCU102_TIMER_ENABLE_INTERVAL_MODE BIT(1)
#define ZCU102_TIMER_ENABLE_DECREMENT_MODE BIT(2)
#define ZCU102_TIMER_ENABLE_MATCH_MODE BIT(3)
// interrupt enable values
#define ZCU102_TIMER_ENABLE_INTERVAL_INTERRUPT BIT(0)
//#define ZCU102_TIMER_ENABLE_


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

static inline uint64_t get_ticks_in_ns(void)
{
    uint64_t value_h = (uint64_t) counter_timer_elapses;
    uint64_t value_l = (uint64_t) timer_regs->cnt_val[TTC_COUNTER_TIMER];

    // TODO: include unhandled IRQ? here or in notified
    uint64_t value_ticks = (value_h << 32) | value_l;

    /* convert from ticks to nanoseconds */
    uint64_t value_whole_seconds = value_ticks / ZCU102_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ticks = value_ticks % ZCU102_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ns = (value_subsecond_ticks * NS_IN_S) / ZCU102_TIMER_TICKS_PER_SECOND;
    uint64_t value_ns = value_whole_seconds * NS_IN_S + value_subsecond_ns;

    return value_ns;
}

void set_timeout(uint64_t timeout)
{
    // as we are using a 32-bit timer, timeouts are done using a MATCH register,
    // but with a check if we havent overflowed

}

#define MAX_TIMEOUTS 6
static uint64_t timeouts[MAX_TIMEOUTS];

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            microkit_notify(i);
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
        set_timeout(next_timeout);
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
    counter_irq = device_resources.irqs[0].id;
    timeout_irq = device_resources.irqs[1].id;

    //uint32_t ctrl = *REG_PTR(REG_COUNTER_CTL);
    uint32_t ctrl = timer_regs->clk_ctrl[TTC_COUNTER_TIMER];
    /* 0th bit set to 1 -> timer counter stopped */
    if (ctrl & 0x1) {
        sddf_dprintf("timer counter is not started\n");
    } else {
        sddf_dprintf("timer counter is started\n");
    }
    sddf_dprintf("REG_COUNTER_CTL is: 0x%x\n", timer_regs->cnt_ctrl[TTC_COUNTER_TIMER]);

    // Table 14-9
    // stop timers
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] = ctrl | BIT(0);
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] = ctrl | BIT(0);
    ctrl = ZCU102_TIMER_CTL_RESET;
    // Reset counter control reg
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
    // Reset counter
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] = ctrl | (1 << 4);
    timer_regs->cnt_ctrl[TTC_TIMEOUT_TIMER] = ctrl | (1 << 4);

    // MATCH MODE
    //// enable match mode
    //sddf_dprintf("ctrl : 0x%x\n", ctrl);
    //ctrl = ctrl | BIT(3);
    //sddf_dprintf("after ctrl : 0x%x\n", ctrl);
    //// enable match interrupt
    //*REG_PTR(REG_COUNTER_IER) = BIT(3) | BIT(1);
    //*REG_PTR(REG_COUNTER_CTL) = ctrl;
    //// Match after 3 s
    //*REG_PTR(REG_COUNTER_MATCH1) = ZCU102_TIMER_TICKS_PER_SECOND;
    //sddf_dprintf("interrupt enable: 0x%x\n", *REG_PTR(REG_COUNTER_IER));
    //sddf_dprintf("match reg: 0x%x match2: 0x%x\n", *REG_PTR(REG_COUNTER_MATCH1), *REG_PTR(REG_COUNTER_MATCH2));
    //// XXX WIP: atm does not match, but does issue IRQ every ~42 seconds (2**32 / ZCU102_TIMER_TICKS_PER_SECOND)

    // ===== INTERVAL MODE ====
    // Set up interval value
    // enable interval interrupt
    //timer_regs->int_en[TTC_COUNTER_TIMER] = ZCU102_TIMER_ENABLE_INTERVAL_INTERRUPT;
    timer_regs->int_en[TTC_COUNTER_TIMER] = ZCU102_TIMER_ENABLE_INTERVAL_INTERRUPT;
    // clock 100MHz ? below will tick every second
    //timer_regs->interval_val[TTC_COUNTER_TIMER] =  0x5F5E100;
    timer_regs->match_1[TTC_COUNTER_TIMER] = ZCU102_TIMER_TICKS_PER_SECOND;

    //ctrl = ctrl | ZCU102_TIMER_ENABLE_INTERVAL_MODE;
    ctrl = ctrl | ZCU102_TIMER_ENABLE_MATCH_MODE;

    // Enable interval mode
    // ===== INTERVAL MODE ====

    //Start the counter
    timer_regs->cnt_ctrl[TTC_COUNTER_TIMER] = ctrl ^ 0x1;
    sddf_dprintf("start counter: 0x%x\n", ctrl ^ 0x1);
    sddf_dprintf("REG_COUNTER_CTL is: 0x%x\n", timer_regs->cnt_ctrl[TTC_COUNTER_TIMER]);

    for (int i = 0; i < 100; i++) {
        sddf_dprintf("i %d, value: 0x%x\n", i, timer_regs->cnt_val[TTC_COUNTER_TIMER]);
    }
}

void notified(microkit_channel ch)
{
    // XXX: allow counter irq and timeout irq. handle both
    assert(ch == counter_irq);
    microkit_deferred_irq_ack(ch);
    sddf_dprintf("Interrupt received!\n");
    sddf_dprintf("Interrupt reg: 0x%x\n", timer_regs->int_sts[TTC_COUNTER_TIMER]);
    sddf_dprintf("Interrupt reg: 0x%x\n", timer_regs->int_sts[TTC_COUNTER_TIMER]);
    sddf_dprintf("counter val: 0x%x\n", timer_regs->cnt_val[TTC_COUNTER_TIMER]);
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
        timeouts[ch] = curr_time + offset_us;
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
