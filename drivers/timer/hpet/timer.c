/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

/* hpet data structures / memory maps */
typedef struct __attribute__((packed)) hpet_timer {
    uint64_t config;
    uint64_t comparator;
    uint64_t fsb_irr;
    char padding[8];
} hpet_timer_t;

/* General HPET config bits */
enum {
    /* 1 if main counter is running and interrupts are enabled */
    ENABLE_CNF = 0,
    /* 1 if LegacyReplacementRoute is being used */
    LEG_RT_CNF = 1
};

/* HPET timer config bits - these can't be changed, but allow us to
 * find out details of the timer */
enum {
    /* 0 is reserved */
    /* 0 if edge triggered, 1 if level triggered. */
    TN_INT_TYPE_CNF = 1,
    /* Set to 1 to cause an interrupt when main timer hits comparator for this timer */
    TN_INT_ENB_CNF = 2,
    /* If this bit is 1 you can write a 1 to it for periodic interrupts,
     * or a 0 for non-periodic interrupts */
    TN_TYPE_CNF = 3,
    /* If this bit is 1, hardware supports periodic mode for this timer */
    TN_PER_INT_CAP = 4,
    /* 1 = timer is 64 bit, 0 = timer is 32 bit */
    TN_SIZE_CAP = 5,
    /* Writing 1 to this bit allows software to directly set a periodic timers accumulator */
    TN_VAL_SET_CNF = 6,
    /* 7 is reserved */
    /* Set this bit to force the timer to be a 32-bit timer (only works on a 64-bit timer) */
    TN_32MODE_CNF = 8,
    /* 5 bit wide field (9:13). Specifies routing for IO APIC if using */
    TN_INT_ROUTE_CNF = 9,
    /* Set this bit to force interrupt delivery to the front side bus, don't use the IO APIC */
    TN_FSB_EN_CNF = 14,
    /* If this bit is one, bit TN_FSB_EN_CNF can be set */
    TN_FSB_INT_DEL_CAP = 15,
    /* Bits 16:31 are reserved */
    /* Read-only 32-bit field that specifies which routes in the IO APIC this timer can be configured
       to take */
    TN_INT_ROUTE_CAP = 32
};

/* MSI registers - used to configure front side bus delivery of the
 * HPET interrupt. This allows us to avoid writing an I/O APIC driver.
 *
 * For details see section 10.10 "APIC message passing mechanism
 * and protocol (P6 family,pentium processors)" in "Intel 64 and IA-32
 * Architectures Software Developers Manual, Volume 3 (3A, 3B & 3C),
 * System Programming Guide" */
/* Message value register layout */
enum {
    /* 0:7 irq_vector */
    IRQ_VECTOR = 0,
    /* 8:10 */
    DELIVERY_MODE = 8,
    /* 11:13 reserved */
    LEVEL_TRIGGER = 14,
    TRIGGER_MODE = 15,
    /* 16:32 reserved */
};

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
#define TIMERS_OFFSET 0x120

#define IRQ_CH 0
uintptr_t HPET_REGION = 0x50000000;

hpet_timer_t *timer_0;
const uint64_t tick_period_fs = 10000000; // main counter tick period in femtoseconds

#define MAX_CLIENTS 6

uint64_t client_timeout[MAX_CLIENTS];
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
    uint64_t time = *(uint64_t *)(HPET_REGION + MAIN_COUNTER_REG);
    __atomic_signal_fence(__ATOMIC_ACQUIRE);
    return ticks_to_ns(time);
}

void set_timeout(uint64_t timeout)
{
    __atomic_signal_fence(__ATOMIC_ACQUIRE);
    timer_0->comparator = ns_to_ticks(timeout);
    __atomic_signal_fence(__ATOMIC_RELEASE);
}

void init(void)
{
    volatile uint64_t *general_config_reg = (void *)HPET_REGION + GENERAL_CONFIG_REG;
    *general_config_reg |= (1ul << ENABLE_CNF);

    timer_0 = (void *)HPET_REGION + TIMERS_OFFSET;
    timer_0->config |= (1ul << TN_FSB_EN_CNF) | (1ul << TN_INT_ENB_CNF);
    timer_0->fsb_irr = ((0x0FEEllu << FIXED) << 32llu) | 0x000 | 0x30;

    __atomic_signal_fence(__ATOMIC_ACQ_REL);

    next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_CLIENTS; i++) {
        client_timeout[i] = UINT64_MAX;
    }

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
        uint64_t timeout = now + delta;

        client_timeout[ch] = timeout;
        if (timeout < next_timeout) {
            next_timeout = timeout;
            set_timeout(timeout);
        }
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

    microkit_deferred_irq_ack(IRQ_CH);

    next_timeout = UINT64_MAX;
    uint64_t now = get_time();
    for (int i = 0; i < MAX_CLIENTS; i++) {
        if (client_timeout[i] <= now) {
            client_timeout[i] = UINT64_MAX;
            microkit_notify(i);
        } else if (client_timeout[i] < next_timeout) {
            next_timeout = client_timeout[i];
        }
    }

    if (next_timeout != UINT64_MAX) {
        set_timeout(next_timeout);
    }
}