/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/arch_counter.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/util/udivmodti4.h>

#define DEBUG_TIMER
#ifdef DEBUG_TIMER
#define LOG_TIMER(...) do{ sddf_printf("TIMER|INFO: ");sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_TIMER(...) do{}while(0)
#endif /* DEBUG_TIMER */

#define LOG_TIMER_WARN(...) do{ sddf_printf("TIMER|WARN: ");sddf_printf(__VA_ARGS__); }while(0)

/* Documents referenced:
 * 1. IA-PC HPET (High Precision Event Timers) Specification
 */

__attribute__((__section__(".device_resources"), retain, used)) device_resources_t device_resources;

/* hpet data structures / memory maps
 * each timer has its own configuration registers:
 *   - Timer n Configuration and Capability Register
 *   - Timer n Comparator Value Register
 *   - Timer n FSB Interrupt Route Register
 * see [1] for more details */
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

/* General HPET capability bits */
/* 1 if device is legacy IRQ replacement capable */
#define LEG_RT_CAP 15
/* 1 if main counter is 64-bit capable */
#define COUNT_SIZE_CAP 13

/* HPET timer config register bits */
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

/* Femtoseconds in nanosecond */
#define FS_IN_NS 1000000

#define HPET_GENERAL_CAP_ID_REG 0x0
#define HPET_GENERAL_CONFIG_REG 0x10
#define HPET_GENERAL_ISR_REG 0x20
#define HPET_MAIN_COUNTER_REG 0xF0
#define HPET_TIMER0_OFFSET 0x100

#define LOW_WORD(x) (x & 0xffffffffffffffff)
#define HIGH_WORD(x) (x >> 64)

// @terryb: remove hard-coded IRQ channel
#define IRQ_CH 0
uintptr_t HPET_REGION = 0x50000000;

volatile hpet_timer_t *timer_0;
uint64_t tick_period_fs; // main counter tick period in femtoseconds
uint64_t tsc_freq = 0;

#define MAX_TIMEOUTS SDDF_TIMER_MAX_CLIENTS

uint64_t timeouts[MAX_TIMEOUTS];
uint64_t next_timeout = UINT64_MAX;

uint64_t get_hpet_ticks(void)
{
    return *(volatile uint64_t *)(HPET_REGION + HPET_MAIN_COUNTER_REG);
}

uint64_t ns_to_hpet_ticks(uint64_t ns)
{
    __uint128_t fs = (__uint128_t)ns * (__uint128_t)FS_IN_NS;
    uint64_t rem = 0;
    return udiv128by64to64(HIGH_WORD(fs), LOW_WORD(fs), tick_period_fs, &rem);
}

uint64_t hpet_ticks_to_ns(uint64_t ticks)
{
    __uint128_t counter_as_fs = (__uint128_t)ticks * (__uint128_t)tick_period_fs;
    uint64_t rem = 0;
    return udiv128by64to64(HIGH_WORD(counter_as_fs), LOW_WORD(counter_as_fs), FS_IN_NS, &rem);
}

void set_timeout(uint64_t timeout)
{
    timer_0->comparator = timeout;
}

static void process_timeouts(uint64_t curr_ticks)
{
    uint64_t next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_ticks) {
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

static uint64_t tsc_ticks_to_ns(uint64_t tsc)
{
    __uint128_t numerator = (__uint128_t)tsc * (__uint128_t)NS_IN_S;
    uint64_t rem = 0;
    return udiv128by64to64(HIGH_WORD(numerator), LOW_WORD(numerator), tsc_freq, &rem);
}

void init(void)
{
    /* Stop main counter */
    volatile uint64_t *general_config_reg = (void *)HPET_REGION + HPET_GENERAL_CONFIG_REG;
    *general_config_reg = 0;

    /* Read the tick period so we can convert between ticks <-> nanoseconds. */
    volatile uint64_t capability = *((uint64_t *)(HPET_REGION + HPET_GENERAL_CAP_ID_REG));
    tick_period_fs = capability >> 32;

    /* Make sure that the main counter is 64-bit wide and legacy IRQ routing capable. */
    assert(capability & BIT(COUNT_SIZE_CAP));
    assert(capability & BIT(LEG_RT_CAP));

    timer_0 = (volatile hpet_timer_t *)(HPET_REGION + HPET_TIMER0_OFFSET);
    uint64_t t0_cfg = timer_0->config;

    /* Make sure the comparator 0 is 64-bit wide */
    assert(t0_cfg & BIT(TN_SIZE_CAP));

    /* Don't deliver IRQ via the Front Side Bus */
    t0_cfg &= ~BIT(TN_FSB_EN_CNF);
    /* Use edge triggered IRQ */
    t0_cfg &= ~BIT(TN_INT_TYPE_CNF);
    /* Turn on IRQ */
    t0_cfg |= BIT(TN_INT_ENB_CNF);
    /* 64-bit wide comparator */
    t0_cfg &= ~BIT(TN_32MODE_CNF);
    /* Non periodic comparator */
    t0_cfg &= ~BIT(TN_TYPE_CNF);

    timer_0->config = t0_cfg;

    /* Reset the main counter */
    *(volatile uint64_t *)(HPET_REGION + HPET_MAIN_COUNTER_REG) = 0;

    /* Enable main counter */
    *general_config_reg |= BIT(ENABLE_CNF);
    /* Use legacy routing, so that comparator 0's IRQ always come in on I/O APIC pin 2 */
    *general_config_reg |= BIT(LEG_RT_CNF);

    next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    microkit_deferred_irq_ack(IRQ_CH);

    /* Detect TSC */
    if (!is_intel_cpu()) {
        LOG_TIMER_WARN("Not an Intel CPU, can't detect TSC frequency, expect performance degradation.\n");
        /* It can be measured, but the measurement procedure is complicated if we want to be accurate.
           See `quick_pit_calibrate()` or `pit_hpet_ptimer_calibrate_cpu()` in Linux arch/x86/kernel/tsc.c */
    } else {
        if (!is_invariant_tsc()) {
            LOG_TIMER_WARN("Invariant TSC not supported, expect performance degradation.\n");
            /* Because SDDF_TIMER_GET_TIME calls will go to the HPET rather than from the TSC.
             * Which is very slow to read. See:
             * https://docs.redhat.com/en/documentation/red_hat_enterprise_linux_for_real_time/7/html/reference_guide/chap-timestamping
             * Their benchmark is reading the timestamp 10,000,000 times.
             * TSC took 0.601s, HPET took 12.263s!
             */
        } else {
            tsc_freq = read_freq();
            if (!tsc_freq) {
                LOG_TIMER_WARN("cannot detect TSC frequency via cpuid, expect performance degradation.\n");
                /* Because same reason as above. */
            } else {
                LOG_TIMER("using TSC as clocksource, HPET as clockevent\n");
                /* Great! Can fastpath time read PPCs. But we still use the HPET for interrupts,
                 * as seL4 uses already used the TSC interrupt mechanism (Local APIC timer) for scheduling. */
            }
        }
    }
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    switch (microkit_msginfo_get_label(msginfo)) {

    case SDDF_TIMER_GET_TIME: {
        if (tsc_freq) {
            microkit_mr_set(0, tsc_ticks_to_ns(read_counter()));
        } else {
            microkit_mr_set(0, hpet_ticks_to_ns(get_hpet_ticks()));
        }
        return microkit_msginfo_new(0, 1);
    }

    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t ticks_now = get_hpet_ticks();
        uint64_t delta = microkit_mr_get(0);
        uint64_t delta_ticks = ns_to_hpet_ticks(delta);

        timeouts[ch] = ticks_now + delta_ticks;
        process_timeouts(ticks_now);
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

    process_timeouts(get_hpet_ticks());
}
