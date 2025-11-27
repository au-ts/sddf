/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <sddf/timer/protocol.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

/* hpet data structures / memory maps
 * each timer has its own configuration registers:
 *   - Timer n Configuration and Capability Register
 *   - Timer n Comparator Value Register
 *   - Timer n FSB Interrupt Route Register
 * see "IA-PC HPET (High Precision Event Timers) Specification" for more details */
typedef struct __attribute__((packed)) hpet_timer {
    uint64_t config;
    uint64_t comparator;
    uint64_t fsb_irr;
    char padding[8];
} hpet_timer_t;

/* General HPET config bits */
/* 1 if main counter is running and interrupts are enabled */
#define ENABLE_CNF 0
/* 1 if LegacyReplacementRoute is being used */
#define LEG_RT_CNF 1

/* HPET timer config bits - these can't be changed, but allow us to
 * find out details of the timer */
/* 0 is reserved */
/* 0 if edge triggered, 1 if level triggered. */
#define TN_INT_TYPE_CNF 1
/* Set to 1 to cause an interrupt when main timer hits comparator for this timer */
#define TN_INT_ENB_CNF 2
/* If this bit is 1 you can write a 1 to it for periodic interrupts,
   or a 0 for non-periodic interrupts */
#define TN_TYPE_CNF 3
/* If this bit is 1, hardware supports periodic mode for this timer */
#define TN_PER_INT_CAP 4
/* 1 = timer is 64 bit, 0 = timer is 32 bit */
#define TN_SIZE_CAP 5
/* Writing 1 to this bit allows software to directly set a periodic timers accumulator */
#define TN_VAL_SET_CNF 6
/* 7 is reserved */
/* Set this bit to force the timer to be a 32-bit timer (only works on a 64-bit timer) */
#define TN_32MODE_CNF 8
/* 5 bit wide field (9:13). Specifies routing for IO APIC if using */
#define TN_INT_ROUTE_CNF 9
/* Set this bit to force interrupt delivery to the front side bus, don't use the IO APIC */
#define TN_FSB_EN_CNF 14
/* If this bit is one, bit TN_FSB_EN_CNF can be set */
#define TN_FSB_INT_DEL_CAP 15
/* Bits 16:31 are reserved */
/* Read-only 32-bit field that specifies which routes in the IO APIC this timer can be configured
   to take */
#define TN_INT_ROUTE_CAP 32

#define HPET_GENERAL_CAP_ID_REG 0x0
#define HPET_GENERAL_CONFIG_REG 0x10
#define HPET_GENERAL_ISR_REG 0x20
#define HPET_MAIN_COUNTER_REG 0xF0
#define HPET_TIMER1_OFFSET 0x120

/* Message address register layout */
enum {
    /* 0:1 reserved */
    DESTINATION_MODE = 2,
    REDIRECTION_HINT = 3,
    /* 4:11 reserved */
    /* 12:19 Destination ID */
    DESTINATION_ID = 12,
    /* 20:31 Fixed value 0x0FEE */
    FIXED = 20
};

#define CAP_ID_REG 0x0
#define GENERAL_CONFIG_REG 0x10
#define GENERAL_ISR_REG 0x20
#define MAIN_COUNTER_REG 0xF0
#define TIMER0_OFFSET 0x100

// @terryb: remove hard-coded IRQ channel
#define IRQ_CH 0
#define IRQ_NUM 0x30
uintptr_t HPET_REGION = 0x50000000;

volatile hpet_timer_t *timer_0;
uint64_t tick_period_fs; // main counter tick period in femtoseconds

#define MAX_TIMEOUTS 6

uint64_t timeouts[MAX_TIMEOUTS];
uint64_t next_timeout = UINT64_MAX;

uint64_t ns_to_ticks(uint64_t ns)
{
    return ns * 1000000 / tick_period_fs;
}

uint64_t ticks_to_ns(uint64_t ticks)
{
    return ticks * tick_period_fs / 1000000;
}

uint64_t get_time(void)
{
    uint64_t time = *(uint64_t *)(HPET_REGION + HPET_MAIN_COUNTER_REG);
    return ticks_to_ns(time);
}

void set_timeout(uint64_t timeout)
{
    timer_0->comparator = ns_to_ticks(timeout);
}

static void process_timeouts(uint64_t curr_time)
{
    uint64_t next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            sddf_notify(i);
            timeouts[i] = UINT64_MAX;
        } else if (timeouts[i] < next_timeout) {
            next_timeout = timeouts[i];
        }
    }

    if (next_timeout != UINT64_MAX) {
        set_timeout(next_timeout);
    }
}

void init(void)
{
    volatile uint64_t capability = *((uint64_t *)(HPET_REGION + CAP_ID_REG));
    tick_period_fs = capability >> 32;
    
    volatile uint64_t *general_config_reg = (void *)HPET_REGION + GENERAL_CONFIG_REG;
    /* Enable main counter */
    *general_config_reg |= (1ul << ENABLE_CNF);
    /* Use legacy routing, so that comparator 0's IRQ always come in on I/O APIC pin 2 */
    *general_config_reg |= (1ul << LEG_RT_CNF);

    timer_0 = (hpet_timer_t *)(HPET_REGION + TIMER0_OFFSET);

    uint64_t t0_cfg = timer_0->config;
    /* Don't deliver IRQ via the Front Side Bus */
    t0_cfg &= ~BIT(TN_FSB_EN_CNF);
    /* Use level IRQ */
    t0_cfg |= BIT(TN_INT_TYPE_CNF);
    /* Switch on IRQ */
    t0_cfg |= BIT(TN_INT_ENB_CNF);
    timer_0->config = t0_cfg;

    __atomic_signal_fence(__ATOMIC_ACQ_REL);

    next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    /* Clear ISR */
    volatile uint64_t *isr = (void *)HPET_REGION + GENERAL_ISR_REG;
    *isr = 1;

    microkit_deferred_irq_ack(IRQ_CH);
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    switch (microkit_msginfo_get_label(msginfo)) {

    case 0: {
        uint64_t now = get_time();
        microkit_mr_set(0, now);
        return microkit_msginfo_new(0, 1);
    }

    case 1: {
        uint64_t delta = microkit_mr_get(0);
        uint64_t now = get_time();

        timeouts[ch] = now + delta;
        process_timeouts(now);
        return microkit_msginfo_new(0, 0);
    }

    default:
        return microkit_msginfo_new(0, 0);
    }
}

void notified(microkit_channel ch)
{
    if (ch != IRQ_CH) {
        return;
    }
    volatile uint64_t *isr = (void *)HPET_REGION + GENERAL_ISR_REG;
    *isr = 1;

    microkit_deferred_irq_ack(IRQ_CH);

    uint64_t now = get_time();

    process_timeouts(now);
}
