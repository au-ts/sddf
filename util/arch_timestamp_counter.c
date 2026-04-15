/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/util/arch_timestamp_counter.h>

// #define DEBUG_ARCH_COUNTER
#ifdef DEBUG_ARCH_COUNTER
#define LOG_ARCH_COUNTER(...) do{ sddf_printf("ARCH_COUNTER|INFO: ");sddf_printf(__VA_ARGS__); }while(0)
#define LOG_ARCH_COUNTER_ERR(...) do{ sddf_printf("ARCH_COUNTER|ERROR: ");sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_ARCH_COUNTER(...) do{}while(0)
#define LOG_ARCH_COUNTER_ERR(...) do{}while(0)
#endif /* DEBUG_ARCH_COUNTER */

#if defined(CONFIG_ARCH_X86)
/* Documents referenced:
 * 1. Intel® 64 and IA-32 Architectures Software Developer’s Manual
 *    Combined Volumes: 1, 2A, 2B, 2C, 2D, 3A, 3B, 3C, 3D, and 4
 *    Order Number: 325462-080US June 2023
 * 2. Linux v6.17 source: native_calibrate_tsc() arch/x86/kernel/tsc.c
 */

/* CPUID related definitions for TSC detection. */

/* [1] "Vendor Identification String" page "3-240 Vol. 2A" */
#define CPUID_VENDOR_ID_LEAF 0x0
#define CPUID_VENDOR_ID_INTEL_EBX 0x756e6547 // "Genu"
#define CPUID_VENDOR_ID_INTEL_ECX 0x6c65746e // "ineI"
#define CPUID_VENDOR_ID_INTEL_EDX 0x49656e69 // "ntel"

/* [1] "Time Stamp Counter and Nominal Core Crystal Clock Information Leaf" page "Vol. 2A 3-231" */
#define CPUID_TSC_LEAF 0x15

/* [1] "Processor Frequency Information Leaf" page "3-232 Vol. 2A" */
#define CPUID_PROC_FREQ_LEAF 0x16

/* [1] "Maximum Input Value for Extended Function CPUID Information." page "Vol. 2A 3-245" */
#define CPUID_MAX_EXT_LEAF 0x80000000

/* [1] "Invariant TSC available if 1" page "Vol. 2A 3-239" */
#define CPUID_INVARIANT_TSC_LEAF 0x80000007
#define CPUID_INVARIANT_TSC_EDX_BIT 8

static inline void cpuid(uint32_t leaf, uint32_t subleaf, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d)
{
    asm volatile("cpuid" : "=a"(*a), "=b"(*b), "=c"(*c), "=d"(*d) : "a"(leaf), "c"(subleaf));
}

bool is_intel_cpu(void)
{
    uint32_t a, b, c, d;
    cpuid(CPUID_VENDOR_ID_LEAF, 0, &a, &b, &c, &d);
    return b == CPUID_VENDOR_ID_INTEL_EBX && d == CPUID_VENDOR_ID_INTEL_EDX && c == CPUID_VENDOR_ID_INTEL_ECX;
}

bool is_invariant_tsc(void)
{
    /* [1] page "Vol. 2A 3-245" */
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

static inline uint64_t rdtsc(void)
{
    uint32_t lo, hi;
    asm volatile("rdtscp" : "=a"(lo), "=d"(hi) : : "ecx");
    asm volatile("lfence" ::: "memory");
    return ((uint64_t)hi << 32) | lo;
}

static uint64_t get_tsc_frequency(void)
{
    uint32_t max_basic_leaf, b, c, d;
    /* Checks whether the CPU expose TSC/Crystal ratio and Crystal frequency via cpuid leaf 0x15. */
    cpuid(CPUID_VENDOR_ID_LEAF, 0, &max_basic_leaf, &b, &c, &d);
    if (max_basic_leaf < CPUID_TSC_LEAF) {
        LOG_ARCH_COUNTER("CPU does not expose TSC leaf.\n");
        return 0;
    }

    uint32_t denominator, numerator, crystal_khz;
    cpuid(CPUID_TSC_LEAF, 0, &denominator, &numerator, &crystal_khz, &d);
    if (!denominator || !numerator) {
        LOG_ARCH_COUNTER("TSC/Crystal ratio cannot be calculated.\n");
        return 0;
    }

    double tsc_to_crystal_freq_ratio = numerator / (double)denominator;

    uint32_t crystal_hz;
    if (!crystal_khz) {
        LOG_ARCH_COUNTER("CPU does not report Crystal frequency, deriving...\n");

        /* From [2]: "Some Intel SoCs like Skylake and Kabylake don't report the crystal
         * clock, but we can easily calculate it to a high degree of accuracy
         * by considering the crystal ratio and the CPU speed." */
        if (max_basic_leaf < CPUID_PROC_FREQ_LEAF) {
            return 0;
        }

        uint32_t proc_base_mhz;
        cpuid(CPUID_PROC_FREQ_LEAF, 0, &proc_base_mhz, &b, &c, &d);
        uint64_t proc_base_hz = proc_base_mhz * 1000ull * 1000ull;
        crystal_hz = proc_base_hz * (1 / tsc_to_crystal_freq_ratio);

        LOG_ARCH_COUNTER("Processor base speed is %u MHz\n", proc_base_mhz);
        LOG_ARCH_COUNTER("Crystal clock is %u Hz\n", crystal_hz);
    } else {
        crystal_hz = crystal_khz * 1000;
    }

    /* From [1]:
     * EAX: denominator of the TSC/”core crystal clock” ratio.
     * EBX: numerator of the TSC/”core crystal clock” ratio.
     * ECX: nominal frequency of the core crystal clock in Hz.
     * So “TSC frequency” = “core crystal clock frequency” * EBX/EAX.
     */

    uint64_t tsc_hz = crystal_hz * tsc_to_crystal_freq_ratio;
    LOG_ARCH_COUNTER("TSC frequency is %u * (%u / %u) = %lu Hz\n", crystal_hz, numerator, denominator, tsc_hz);
    return tsc_hz;
}

uint64_t read_counter(void)
{
    return rdtsc();
}

static bool checked_tsc_frequency = false;
static bool cached_frequency = false;
static uint64_t cached_tsc_frequency;
/*
 * On x86 calculating the frequency of the tsc uses cpuid which is a serialising instruction
 * https://www.google.com/url?sa=t&source=web&rct=j&opi=89978449&url=https://cdrdv2-public.intel.com/789589/334569-sdm-vol-2d.pdf&ved=2ahUKEwi4qufojomVAxUPUPUHHVNyElwQFnoECB0QAQ&usg=AOvVaw2qnfp2RSVGg-7BJcEpfHIn
 * Therefore if the TSC is invariant i.e. will not change dynamically then
 * we cache the frequency for performance reasons.
 *
 * NOTE: Do not use this function in a concurrent environment.
 */
uint64_t read_freq(void)
{
    if (!checked_tsc_frequency) {
        if (is_invariant_tsc()) {
            cached_tsc_frequency = get_tsc_frequency();
            cached_frequency = true;
        }
        checked_tsc_frequency = true;
    }
    if (likely(cached_frequency)) {
        return cached_tsc_frequency;
    }
    return get_tsc_frequency();
}

#elif defined(CONFIG_ARCH_AARCH64)
uint64_t read_counter(void)
{
    uint64_t v;
    asm volatile("isb" ::: "memory");
    asm volatile("mrs %0, cntpct_el0" : "=r"(v)::"memory");
    asm volatile("isb" ::: "memory");
    return v;
}

uint64_t read_freq(void)
{
    uint64_t v;
    asm volatile("mrs %0, cntfrq_el0" : "=r"(v));
    return v;
}

#elif defined(CONFIG_ARCH_RISCV)
__attribute__((__section__(".arch_counter_config"))) riscv_timestamp_counter_config_t timestamp_counter_config;

uint64_t read_counter(void)
{
    uint64_t v;
    asm volatile("fence.i" ::: "memory");
    asm volatile("fence r, r" ::: "memory");
    asm volatile("rdtime %0" : "=r"(v)::"memory");
    asm volatile("fence.i" ::: "memory");
    asm volatile("fence r, r" ::: "memory");
    return v;
}

static bool checked_config = false;
uint64_t read_freq(void)
{
    if (likely(checked_config)) {
        return timestamp_counter_config.frequency;
    } else if (memcmp(timestamp_counter_config.magic, COUNTER_UTIL_MAGIC, COUNTER_UTIL_MAGIC_LEN)) {
        LOG_ARCH_COUNTER_ERR("RISC-V requires an timestamp_counter_config struct\n");
        return 0;
    }

    checked_config = true;
    return timestamp_counter_config.frequency;
}

#endif
