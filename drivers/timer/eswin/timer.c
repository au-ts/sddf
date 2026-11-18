/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/timer/timer_driver.h>

/*
 * https://www.sifive.com/document-file/eic7700x-datasheet
 */

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

/*
 * The EIC7700X TIMER module contains 8 down-counting 32-bit timers (EIC7700X SoC Manual 12.8).
 * All share an interrupt line from the PLIC.
 */
struct timer_regs {
    uint32_t load_count; /* 0x00: TimerNLoadCount */
    uint32_t val;        /* 0x04: TimerNCurrentValue. Read only. */
    uint32_t ctrl;       /* 0x08: TimerNControlReg */
    uint32_t eoi;        /* 0x0c: TimerNEOI. Reading clears the interrupt. */
    uint32_t int_status; /* 0x10: TimerNIntStatus. Read only. */
};

#define TIMER_N_REGS_SIZE 0x14

#define TIMER_CTRL_ENABLE BIT(0)
/* 0: free-running (reloads the maximum value), 1: user-defined (reloads TimerNLoadCount) */
#define TIMER_CTRL_MODE_USER_DEFINED BIT(1)
#define TIMER_CTRL_INT_MASK BIT(2)

#define TIMER_INT_STATUS_ACTIVE BIT(0)

volatile struct timer_regs *counter_timer_regs;
volatile struct timer_regs *timeout_timer_regs;

/* We use separate timers (but on the same hardware device) for the counter and setting timeouts. */
#define TIMER_COUNTER 1
#define TIMER_TIMEOUT 2

#define TIMER_MAX_TICKS UINT32_MAX

// TODO: pass in from DTS via Acacia
#ifdef CONFIG_PLAT_HIFIVE_P550
/* 24 MHz frequency. Obtained from 'timebase-frequency = <0xf4240>' in the DTS. */
#define ESWIN_TIMER_CLK_FREQ 24000000
#endif

#define CLIENT_CH_START 1
#define MAX_TIMEOUTS SDDF_TIMER_MAX_CLIENTS
static uint64_t timeouts[MAX_TIMEOUTS];

/* Keep track of how many timer overflows have occured.
 * Used as the most significant segment of ticks.
 * We need to keep track of this state as the value register is only
 * 32 bits as opposed to the common 64 bit timer value regsiters found
 * on other devices.
 */
uint32_t counter_timer_elapses = 0;
uint32_t timeout_timer_elapses = 0;

static uint64_t get_ticks_in_ns(void)
{
    /* the timer value counts down from the load value */
    uint64_t value_l = (TIMER_MAX_TICKS - counter_timer_regs->val);
    uint64_t value_h = counter_timer_elapses;

    /* Account for potential pending counter IRQ */
    if (counter_timer_regs->int_status & TIMER_INT_STATUS_ACTIVE) {
        value_h += 1;
        value_l = (uint64_t)(TIMER_MAX_TICKS - counter_timer_regs->val);
    }

    uint64_t value_ticks = (value_h << 32) | value_l;

    return ticks_to_ns(value_ticks, ESWIN_TIMER_CLK_FREQ);
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

    /* The new count is loaded from TimerNLoadCount when the timer goes from disabled to enabled. */
    timeout_timer_regs->ctrl = TIMER_CTRL_MODE_USER_DEFINED;

    /* Leave the timer disabled when nothing is pending, as user-defined mode periodically reloads. */
    if (next_timeout != UINT64_MAX) {
        uint64_t ns = next_timeout - curr_time;

        timeout_timer_elapses = 0;

        uint64_t num_ticks = ns_to_ticks(ns, ESWIN_TIMER_CLK_FREQ);

        if (num_ticks > TIMER_MAX_TICKS) {
            num_ticks = TIMER_MAX_TICKS;
        } else if (num_ticks == 0) {
            num_ticks = 1;
        }

        timeout_timer_regs->load_count = num_ticks;
        timeout_timer_regs->ctrl = TIMER_CTRL_MODE_USER_DEFINED | TIMER_CTRL_ENABLE;
    }
}

void notified(microkit_channel ch)
{
    assert(ch == device_resources.irqs[0].id);

    if (counter_timer_regs->int_status & TIMER_INT_STATUS_ACTIVE) {
        counter_timer_elapses += 1;
        counter_timer_regs->eoi;
    }

    if (timeout_timer_regs->int_status & TIMER_INT_STATUS_ACTIVE) {
        timeout_timer_elapses += 1;
        /* Clear before reprogramming so that an interrupt for the next timeout is not lost. */
        timeout_timer_regs->eoi;
        uint64_t curr_time = get_ticks_in_ns();
        process_timeouts(curr_time);
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
        uint64_t offset_ns = seL4_GetMR(0);
        timeouts[ch - CLIENT_CH_START] = curr_time + offset_ns;
        process_timeouts(curr_time);
        break;
    }
    default:
        sddf_dprintf("TIMER DRIVER|ERROR: Unknown request %lu to timer from channel %u\n",
                     microkit_msginfo_get_label(msginfo), ch);
        break;
    }

    return microkit_msginfo_new(0, 0);
}

void init(void)
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    void *regs_base = device_resources.regions[0].region.vaddr;
    counter_timer_regs = regs_base + (TIMER_COUNTER - 1) * TIMER_N_REGS_SIZE;
    timeout_timer_regs = regs_base + (TIMER_TIMEOUT - 1) * TIMER_N_REGS_SIZE;

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    /* Disable both timers and reset both timers initially */
    counter_timer_regs->ctrl = 0;
    timeout_timer_regs->ctrl = TIMER_CTRL_MODE_USER_DEFINED;
    counter_timer_regs->eoi;
    timeout_timer_regs->eoi;

    /* Set counter to free running. */
    counter_timer_regs->load_count = TIMER_MAX_TICKS;
    counter_timer_regs->ctrl = TIMER_CTRL_ENABLE;
}
