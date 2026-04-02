/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/timer/timer_driver.h>
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
 * 2. Intel® 64 and IA-32 Architectures Software Developer’s Manual
 *    Combined Volumes: 1, 2A, 2B, 2C, 2D, 3A, 3B, 3C, 3D, and 4
 *    Order Number: 325462-080US June 2023
 * 3. Linux v6.17 source: native_calibrate_tsc() arch/x86/kernel/tsc.c
 */

__attribute__((__section__(".device_resources"), retain, used)) device_resources_t device_resources;
__attribute__((__section__(".timer_driver_config"))) timer_driver_config_t config;

/* CPUID related definitions for TSC detection. */

/* [2] "Vendor Identification String" page "3-240 Vol. 2A" */
#define CPUID_VENDOR_ID_LEAF 0x0
#define CPUID_VENDOR_ID_INTEL_EBX 0x756e6547 // "Genu"
#define CPUID_VENDOR_ID_INTEL_ECX 0x6c65746e // "ineI"
#define CPUID_VENDOR_ID_INTEL_EDX 0x49656e69 // "ntel"

/* [2] "Time Stamp Counter and Nominal Core Crystal Clock Information Leaf" page "Vol. 2A 3-231" */
#define CPUID_TSC_LEAF 0x15

/* [2] "Processor Frequency Information Leaf" page "3-232 Vol. 2A" */
#define CPUID_PROC_FREQ_LEAF 0x16

/* [2] "Maximum Input Value for Extended Function CPUID Information." page "Vol. 2A 3-245" */
#define CPUID_MAX_EXT_LEAF 0x80000000

/* [2] "Invariant TSC available if 1" page "Vol. 2A 3-239" */
#define CPUID_INVARIANT_TSC_LEAF 0x80000007
#define CPUID_INVARIANT_TSC_EDX_BIT 8

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
static sddf_timer_freq_hz_t hpet_clk_freq = 0;
static sddf_timer_freq_hz_t tsc_clk_freq = 0;

uint64_t target_timeout = UINT64_MAX;

static inline uint64_t rdtsc(void)
{
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

static inline void cpuid(uint32_t leaf, uint32_t subleaf, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d)
{
    __asm__ __volatile__("cpuid" : "=a"(*a), "=b"(*b), "=c"(*c), "=d"(*d) : "a"(leaf), "c"(subleaf));
}

uint64_t get_hpet_ticks(void)
{
    return *(volatile uint64_t *)(HPET_REGION + HPET_MAIN_COUNTER_REG);
}

uint64_t ns_to_hpet_ticks(uint64_t ns)
{
    return ns_to_tick_cached(ns, 0, hpet_clk_freq);
}

uint64_t hpet_ticks_to_ns(uint64_t ticks)
{
    return tick_to_ns_cached(ticks, 0, hpet_clk_freq);
}

void set_timeout(uint64_t timeout)
{
    timer_0->comparator = timeout;
}

static void process_target_timeout(uint64_t curr_ticks)
{
    if (target_timeout <= curr_ticks) {
        sddf_notify(config.virt_id);
        // Update "current" time page with virt
        set_shared_time_page(get_current_time());
        target_timeout = UINT64_MAX;
    }

    if (target_timeout != UINT64_MAX) {
        set_timeout(target_timeout);
    }
}

static bool is_intel_cpu(void)
{
    uint32_t a, b, c, d;
    cpuid(CPUID_VENDOR_ID_LEAF, 0, &a, &b, &c, &d);
    return b == CPUID_VENDOR_ID_INTEL_EBX && d == CPUID_VENDOR_ID_INTEL_EDX && c == CPUID_VENDOR_ID_INTEL_ECX;
}

static bool is_invariant_tsc(void)
{
    /* [2] page "Vol. 2A 3-245" */
    /* Check "Maximum Input Value for Extended Function CPUID Information." */
    uint32_t max_ext_leaf, a, b, c, d;
    cpuid(CPUID_MAX_EXT_LEAF, 0, &max_ext_leaf, &b, &c, &d);

    if (max_ext_leaf < CPUID_INVARIANT_TSC_LEAF) {
        return false;
    }

    /* Then check whether Invariant TSC is true */
    uint32_t invariant_tsc;
    cpuid(CPUID_INVARIANT_TSC_LEAF, 0, &a, &b, &c, &invariant_tsc);
    return !!(invariant_tsc & BIT(CPUID_INVARIANT_TSC_EDX_BIT));
}

static uint64_t get_tsc_frequency(void)
{
    uint32_t max_basic_leaf, b, c, d;
    /* Checks whether the CPU expose TSC/Crystal ratio and Crystal frequency via cpuid leaf 0x15. */
    cpuid(CPUID_VENDOR_ID_LEAF, 0, &max_basic_leaf, &b, &c, &d);
    if (max_basic_leaf < CPUID_TSC_LEAF) {
        LOG_TIMER("CPU does not expose TSC leaf.\n");
        return 0;
    }

    uint32_t denominator, numerator, crystal_khz;
    cpuid(CPUID_TSC_LEAF, 0, &denominator, &numerator, &crystal_khz, &d);
    if (!denominator || !numerator) {
        LOG_TIMER("TSC/Crystal ratio cannot be calculated.\n");
        return 0;
    }

    uint32_t crystal_hz;
    if (!crystal_khz) {
        LOG_TIMER("CPU does not report Crystal frequency, deriving...\n");

        /* From [3]: "Some Intel SoCs like Skylake and Kabylake don't report the crystal
         * clock, but we can easily calculate it to a high degree of accuracy
         * by considering the crystal ratio and the CPU speed." */
        if (max_basic_leaf < CPUID_PROC_FREQ_LEAF) {
            return 0;
        }

        uint32_t proc_base_mhz;
        cpuid(CPUID_PROC_FREQ_LEAF, 0, &proc_base_mhz, &b, &c, &d);
        crystal_hz = proc_base_mhz * 1000 * 1000 * (denominator / (double)numerator);

        LOG_TIMER("Processor base speed is %u MHz\n", proc_base_mhz);
        LOG_TIMER("Crystal clock is %u Hz\n", crystal_hz);
    } else {
        crystal_hz = crystal_khz * 1000;
    }

    /* From [2]:
     * EAX: denominator of the TSC/”core crystal clock” ratio.
     * EBX: numerator of the TSC/”core crystal clock” ratio.
     * ECX: nominal frequency of the core crystal clock in Hz.
     * So “TSC frequency” = “core crystal clock frequency” * EBX/EAX.
     */

    uint64_t tsc_hz = (uint64_t)crystal_hz * (numerator / (double)denominator);
    LOG_TIMER("TSC frequency is %u * (%u / %u) = %lu Hz\n", crystal_hz, numerator, denominator, tsc_hz);
    return tsc_hz;
}

static uint64_t tsc_ticks_to_ns(uint64_t tsc)
{
    return tick_to_ns_cached(tsc, 0, tsc_clk_freq);
}

void init(void)
{
    /* Stop main counter */
    volatile uint64_t *general_config_reg = (void *)HPET_REGION + HPET_GENERAL_CONFIG_REG;
    *general_config_reg = 0;

    /* Read the tick period so we can convert between ticks <-> nanoseconds. */
    volatile uint64_t capability = *((uint64_t *)(HPET_REGION + HPET_GENERAL_CAP_ID_REG));
    tick_period_fs = capability >> 32;
    hpet_clk_freq = FS_IN_S / tick_period_fs;
    sddf_dprintf("Found clk_freq as %u\n", hpet_clk_freq);

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
            tsc_clk_freq = get_tsc_frequency();
            if (!tsc_clk_freq) {
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

void notified(microkit_channel ch)
{
    if (ch != IRQ_CH) {
        return;
    }

    microkit_deferred_irq_ack(IRQ_CH);

    // IMPORTANT: use hpet time, not tsc time for handling timeouts.
    process_target_timeout(get_hpet_ticks());
    set_shared_time_page(get_current_time());
}

// Protocol common functions
bool set_new_timeout(uint64_t timestamp)
{
    // This timer uses ticks for timeouts, not nanoseconds.
    uint64_t curr_time_hpet = get_hpet_ticks();

    if (tsc_clk_freq) {
        uint64_t curr_time_tsc = tsc_ticks_to_ns(rdtsc());
        // The timebase is different for the hpet, so we need to create an hpet-equivalent
        // absolute timestamp. INVARIANT: timestamp > tsc_time. Guaranteed by common protected()
        // logic.
        assert(timestamp > curr_time_tsc);
        LOG_TIMER_DRIVER("hpet time: %zu, tsc time: %zu, target: %zu\n", curr_time_hpet, curr_time_tsc, timestamp);
        uint64_t delta_hpet = ns_to_hpet_ticks(timestamp - curr_time_tsc);
        uint64_t hpet_timestamp = curr_time_hpet + delta_hpet;
        LOG_TIMER_DRIVER("delta: %zu, hpet target timestamp: %zu\n", delta_hpet, hpet_timestamp);
        // Convert to ticks and set as target
        target_timeout = hpet_timestamp;
    } else {
        LOG_TIMER_DRIVER("setting timeout directly from hpet...\n");
        target_timeout = ns_to_hpet_ticks(timestamp);
    }
    LOG_TIMER_DRIVER("Setting timeout for %zu ticks\n", target_timeout);

    process_target_timeout(curr_time_hpet);
    return true;
}

uint64_t get_current_time(void)
{
    uint64_t time = 0;
    if (tsc_clk_freq) {
        time = tsc_ticks_to_ns(rdtsc());
    } else {
        time = hpet_ticks_to_ns(get_hpet_ticks());
    }
    return time;
}
