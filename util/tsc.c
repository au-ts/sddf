/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/util/arch_counter.h>

#define DEBUG_TSC
#ifdef DEBUG_TSC
#define LOG_TSC(...) do{ sddf_printf("TSC|INFO: ");sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_TSC(...) do{}while(0)
#endif /* DEBUG_TSC*/

#if defined(CONFIG_ARCH_X86)

/* Documents referenced:
 * 1. IA-PC HPET (High Precision Event Timers) Specification
 * 2. Intel® 64 and IA-32 Architectures Software Developer’s Manual
 *    Combined Volumes: 1, 2A, 2B, 2C, 2D, 3A, 3B, 3C, 3D, and 4
 *    Order Number: 325462-080US June 2023
 * 3. Linux v6.17 source: native_calibrate_tsc() arch/x86/kernel/tsc.c
 */

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

static inline void cpuid(uint32_t leaf, uint32_t subleaf, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d)
{
    __asm__ __volatile__("cpuid" : "=a"(*a), "=b"(*b), "=c"(*c), "=d"(*d) : "a"(leaf), "c"(subleaf));
}

bool is_intel_cpu(void)
{
    uint32_t a, b, c, d;
    cpuid(CPUID_VENDOR_ID_LEAF, 0, &a, &b, &c, &d);
    return b == CPUID_VENDOR_ID_INTEL_EBX && d == CPUID_VENDOR_ID_INTEL_EDX && c == CPUID_VENDOR_ID_INTEL_ECX;
}

bool is_invariant_tsc(void)
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

static uint64_t rdtsc(void)
{
    uint32_t lo, hi;
    __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

static bool cached_frequency = false;
static uint64_t get_tsc_frequency(void)
{
    cached_frequency = true;
    uint32_t max_basic_leaf, b, c, d;
    /* Checks whether the CPU expose TSC/Crystal ratio and Crystal frequency via cpuid leaf 0x15. */
    cpuid(CPUID_VENDOR_ID_LEAF, 0, &max_basic_leaf, &b, &c, &d);
    if (max_basic_leaf < CPUID_TSC_LEAF) {
        LOG_TSC("CPU does not expose TSC leaf.\n");
        return 0;
    }

    uint32_t denominator, numerator, crystal_khz;
    cpuid(CPUID_TSC_LEAF, 0, &denominator, &numerator, &crystal_khz, &d);
    if (!denominator || !numerator) {
        LOG_TSC("TSC/Crystal ratio cannot be calculated.\n");
        return 0;
    }

    double tsc_to_crystal_freq_ratio = numerator / (double)denominator;

    uint32_t crystal_hz;
    if (!crystal_khz) {
        LOG_TSC("CPU does not report Crystal frequency, deriving...\n");

        /* From [3]: "Some Intel SoCs like Skylake and Kabylake don't report the crystal
         * clock, but we can easily calculate it to a high degree of accuracy
         * by considering the crystal ratio and the CPU speed." */
        if (max_basic_leaf < CPUID_PROC_FREQ_LEAF) {
            return 0;
        }

        uint32_t proc_base_mhz;
        cpuid(CPUID_PROC_FREQ_LEAF, 0, &proc_base_mhz, &b, &c, &d);
        uint64_t proc_base_hz = proc_base_mhz * 1000ull * 1000ull;
        crystal_hz = proc_base_hz * (1 / tsc_to_crystal_freq_ratio);

        LOG_TSC("Processor base speed is %u MHz\n", proc_base_mhz);
        LOG_TSC("Crystal clock is %u Hz\n", crystal_hz);
    } else {
        crystal_hz = crystal_khz * 1000;
    }

    /* From [2]:
     * EAX: denominator of the TSC/”core crystal clock” ratio.
     * EBX: numerator of the TSC/”core crystal clock” ratio.
     * ECX: nominal frequency of the core crystal clock in Hz.
     * So “TSC frequency” = “core crystal clock frequency” * EBX/EAX.
     */

    uint64_t tsc_hz = crystal_hz * tsc_to_crystal_freq_ratio;
    LOG_TSC("TSC frequency is %u * (%u / %u) = %lu Hz\n", crystal_hz, numerator, denominator, tsc_hz);
    return tsc_hz;
}

uint64_t read_counter(void)
{
    return rdtsc();
}

static uint64_t cached_tsc_frequency;
uint64_t read_freq(void)
{
    if (cached_frequency) {
        return cached_tsc_frequency;
    }
    return get_tsc_frequency();
}

#elif defined(CONFIG_ARCH_AARCH64)

uint64_t read_counter(void)
{
    uint64_t v;
    __asm__ volatile("mrs %0, cntpct_el0" : "=r"(v));
    return v;
}

uint64_t read_freq(void)
{
    uint64_t v;
    __asm__ volatile("mrs %0, cntfrq_el0" : "=r"(v));
    return v;
}

#endif
