/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stddef.h>
#include "events.h"

/* A counter is an index to a performance counter on a platform.
 * The max counter index is sizeof(seL4_Word) */
typedef uint64_t counter_t;
/* A counter_bitfield is used to select multiple counters.
 * Each bit corresponds to a counter id */
typedef uint64_t counter_bitfield_t;

/* An event id is the hardware id of an event.
 * See the events.h for your architecture for specific events, caveats,
 * gotchas, and other trickery. */
typedef uint64_t event_id_t;

//function attributes
//ultra-short, time-sensitive functions
#define FASTFN inline __attribute__((always_inline))

//short, cache-sensitive functions (note: short means one cache line)
#define CACHESENSFN __attribute__((noinline, aligned(64)))

//functions that will be passed to seL4_DebugRun() -- fast, but obviously not inlined
#define KERNELFN __attribute__((noinline, flatten))

#define BIT(n) (1ul << (n))
#define IN_TX_BIT BIT(0)
#define IN_TXCP_BIT BIT(1)

//CPUID leaf node numbers
enum {
    IA32_CPUID_LEAF_BASIC    = 0,
    IA32_CPUID_LEAF_MODEL    = 1,
    IA32_CPUID_LEAF_PMC      = 0xA,
    IA32_CPUID_LEAF_EXTENDED = 0x80000000,
};

//CPUID.0 "GenuineIntel"
#define IA32_CPUID_BASIC_MAGIC_EBX 0x756E6547
#define IA32_CPUID_BASIC_MAGIC_ECX 0x6C65746E
#define IA32_CPUID_BASIC_MAGIC_EDX 0x49656E69

//CPUID.1 Family and Model ID macros and type.
#define FAMILY(x) (  (x).family == 0xF                       ? ( (x).ex_family      + (x).family) : (x).family )
#define MODEL(x)  ( ((x).family == 0xF || (x).family == 0x6) ? (((x).ex_model << 4) + (x).model ) : (x).model  )
#define IA32_CPUID_FAMILY_P6 0x6
typedef union {
    struct {
        uint64_t stepping  : 4;
        uint64_t model     : 4;
        uint64_t family    : 4;
        uint64_t type      : 2;
        uint64_t reserved1 : 2;
        uint64_t ex_model  : 4;
        uint64_t ex_family : 8;
        uint64_t reserved2 : 4;
    };
    uint32_t raw;
} ia32_cpuid_model_info_t;

//CPUID.PMC Performance-monitoring macros and types
typedef union {
    struct {
        uint8_t pmc_version_id;
        uint8_t gp_pmc_count_per_core;
        uint8_t gp_pmc_bit_width;
        uint8_t ebx_bit_vector_length;
    };
    uint32_t  raw;
} ia32_cpuid_leaf_pmc_eax_t;

//Control-register constants
#define IA32_CR4_PCE               8

//PMC MSRs
#define IA32_MSR_PMC_PERFEVTSEL_BASE 0x186
#define IA32_MSR_PMC_PERFEVTCNT_BASE 0x0C1
typedef union {
    struct {
        uint16_t event;
        union {
            struct {
                uint8_t USR : 1;
                uint8_t OS  : 1;
                uint8_t E   : 1;
                uint8_t PC  : 1;
                uint8_t INT : 1;
                uint8_t res : 1;
                uint8_t EN  : 1;
                uint8_t INV : 1;
            };
            uint8_t flags;
        };
        uint8_t cmask;
    };
    uint32_t raw;
} ia32_pmc_perfevtsel_t;

//Convenient execution of CPUID instruction. The first version isn't volatile, so is for querying the processor; the second version just serialises.
//This looks slow, but gcc inlining is smart enough to optimise away all the memory references, and takes unused information into account.
static FASTFN void sel4bench_private_cpuid(uint32_t leaf, uint32_t subleaf, uint32_t * eax, uint32_t * ebx, uint32_t * ecx, uint32_t * edx)
{
    asm (
        "cpuid"
        : "=a"(*eax)    /* output eax */
        , "=b"(*ebx)    /* output ebx */
        , "=c"(*ecx)    /* output ecx */
        , "=d"(*edx)    /* output edx */
        : "a" (leaf)    /* input query leaf */
        , "c" (subleaf) /* input query subleaf */
    );
}
static FASTFN void sel4bench_private_cpuid_serial()
{
    //set leaf and subleaf to 0 for predictability
    uint32_t eax = 0;
    uint32_t ecx = 0;
    asm volatile (
        "cpuid"
        : "+a"(eax)       /* eax = 0 and gets clobbered */
        , "+c"(ecx)       /* ecx = 0 and gets clobbered */
        :                 /* no other inputs to this version */
        : "%ebx"          /* clobber ebx */
        , "%edx"          /* clobber edx */
        , "cc"            /* clobber condition code */
    );
}
static FASTFN void sel4bench_private_lfence()
{
    asm volatile("lfence");
}

static FASTFN uint64_t sel4bench_private_rdtsc()
{
    uint32_t lo, hi;
    asm volatile (
        "rdtsc"
        : "=a"(lo), "=d"(hi)
    );
    return (((uint64_t)hi << 32ull) | (uint64_t)lo);
}

static FASTFN uint64_t sel4bench_private_rdpmc(uint32_t counter)
{
    uint32_t hi, lo;
    asm volatile (
        "rdpmc"
        : "=a"(lo), "=d"(hi)
        : "c"(counter)
    );
    return (((uint64_t)hi << 32ull) | (uint64_t)lo);
}

//Serialization instruction for before and after reading PMCs
//See comment in arch/sel4bench.h for details.
#ifdef SEL4BENCH_STRICT_PMC_SERIALIZATION
#define sel4bench_private_serialize_pmc sel4bench_private_cpuid_serial
#else //SEL4BENCH_STRICT_PMC_SERIALIZATION
#define sel4bench_private_serialize_pmc sel4bench_private_lfence
#endif //SEL4BENCH_STRICT_PMC_SERIALIZATION

/* Hide these definitions if using kernel exported PMC to prevent warnings */
#ifndef CONFIG_EXPORT_PMC_USER
//enable user-level pmc access
static KERNELFN void sel4bench_private_enable_user_pmc(void* arg)
{
#ifdef CONFIG_ARCH_X86_64

    uint64_t dummy;
    asm volatile (
        "movq   %%cr4, %0;"
        "orq    %[pce], %0;"
        "movq   %0, %%cr4;"
        : "=r" (dummy)
        : [pce] "i" BIT(IA32_CR4_PCE)
        : "cc"
    );
#else

    uint32_t dummy;
    asm volatile (
        "movl %%cr4, %0;"               /* read CR4 */
        "orl %[pce], %0;"               /* enable PCE flag */
        "movl %0, %%cr4;"               /* write CR4 */
        : "=r" (dummy)                  /* fake output to ask GCC for a register */
        : [pce] "i" BIT(IA32_CR4_PCE) /* input PCE flag */
        : "cc"                          /* clobber condition code */
    );
#endif
}

//disable user-level pmc access
static KERNELFN void sel4bench_private_disable_user_pmc(void* arg)
{
#ifdef CONFIG_ARCH_X86_64
    uint64_t dummy;
    asm volatile (
        "movq   %%cr4, %0;"
        "andq   %[pce], %0;"
        "movq   %0, %%cr4;"
        : "=r" (dummy)
        : [pce] "i" (~BIT(IA32_CR4_PCE))
        : "cc"
    );

#else
    uint32_t dummy;
    asm volatile (
        "movl %%cr4, %0;"                  /* read CR4 */
        "andl %[pce], %0;"                 /* enable PCE flag */
        "movl %0, %%cr4;"                  /* write CR4 */
        : "=r" (dummy)                     /* fake output to ask GCC for a register */
        : [pce] "i" (~BIT(IA32_CR4_PCE)) /* input PCE flag */
        : "cc"                             /* clobber condition code */
    );
#endif
}
#endif

#ifndef CONFIG_KERNEL_X86_DANGEROUS_MSR
//read an MSR
static KERNELFN void sel4bench_private_rdmsr(void* arg)
{
    uint32_t* msr = (uint32_t*)arg;

    asm volatile (
        "rdmsr"
        : "=a" (msr[1]) /* output low */
        , "=d" (msr[2]) /* output high */
        :  "c" (msr[0]) /* input MSR index */
    );
}

//write an MSR
static KERNELFN void sel4bench_private_wrmsr(void* arg)
{
    uint32_t* msr = (uint32_t*)arg;

    asm volatile (
        "wrmsr"
        :               /* no output */
        : "a" (msr[1])  /* input low */
        , "d" (msr[2])  /* input high */
        , "c" (msr[0])  /* input MSR index */
    );
}
#endif

//generic event tables for lookup fn below
//they use direct event numbers, rather than the constants in events.h, because it's smaller
static uint64_t SEL4BENCH_IA32_WESTMERE_EVENTS[5] = {
    0x0280, //CACHE_L1I_MISS
    0x0151, //CACHE_L1D_MISS, must use counter 0 or 1
    0x20C8, //TLB_L1I_MISS
    0x80CB, //TLB_L1D_MISS
    0x5FCB  //SEL4BENCH_IA32_WESTMERE_EVENT_CACHE_|{L1D_HIT,L2_HIT,L3P_HIT,L3_HIT,L3_MISS,LFB_HIT}_R
};
static uint64_t SEL4BENCH_IA32_NEHALEM_EVENTS[5] = {
    0x0280, //CACHE_L1I_MISS
    0x0151, //CACHE_L1D_MISS, must use counter 0 or 1
    0x20C8, //TLB_L1I_MISS
    0x80CB, //TLB_L1D_MISS
    0x5FCB  //SEL4BENCH_IA32_NEHALEM_EVENT_CACHE_|{L1D_HIT,L2_HIT,L3P_HIT,L3_HIT,L3_MISS,LFB_HIT}_R
};
static uint64_t SEL4BENCH_IA32_CORE2_EVENTS[5] = {
    0x0081, //CACHE_L1I_MISS
    0x01CB, //CACHE_L1D_MISS, must use counter 0
    0x00C9, //TLB_L1I_MISS
    0x10CB, //TLB_L1D_MISS, must use counter 0
    0x03C0  //SEL4BENCH_IA32_CORE2_EVENT_RETIRE_MEMORY_|{READ,WRITE}
};
static uint64_t SEL4BENCH_IA32_CORE_EVENTS[5] = {
    0x0081, //CACHE_L1I_MISS
    0x0000, //CACHE_L1D_MISS, not available on CORE
    0x0085, //TLB_L1I_MISS
    0x0049, //TLB_L1D_MISS
    0x0143  //MEMORY_ACCESS
};
static uint64_t SEL4BENCH_IA32_P6_EVENTS[5] = {
    0x0081, //CACHE_L1I_MISS
    0x0045, //CACHE_L1D_MISS
    0x0085, //TLB_L1I_MISS
    0x0000, //TLB_L1D_MISS, not available on P6
    0x0043  //MEMORY_ACCESS
};
static uint64_t SEL4BENCH_IA32_HASWELL_EVENTS[5] = {
    0x0280, //CACHE_L1I_MISS
    0x0151, //CACHE_L1D_MISS, must use counter 0 or 1
    0x0085, //TLB_L1I_MISS
    0x0049, //TLB_L1D_MISS
    0x412E  //LLC_MISS
};
static uint64_t SEL4BENCH_IA32_BROADWELL_EVENTS[5] = {
    0x0280, //ICACHE.MISSES
    0x0151, //L1D.REPLACEMENT
    0x2185, //ITLB_MISSES.MISS_CAUSES_A_WALK | ITLB_MISSES.STLB_HIT_4K
    0x0000, //No combined load/store dTLB miss counter available
    0x412E  //LONGEST_LAT_CACHE.MISS
};
static uint64_t SEL4BENCH_IA32_SKYLAKE_EVENTS[5] = {
    0x0000, //No combined tag/data iCache miss counter available
    0x0151, //L1D.REPLACEMENT
    0x2185, //ITLB_MISSES.MISS_CAUSES_A_WALK | ITLB_MISSES.STLB_HIT
    0x0000, //No combined load/store dTLB miss counter available
    0x412E  //LONGEST_LAT_CACHE.MISS
};

static FASTFN uint64_t sel4bench_private_lookup_event(event_id_t event)
{
    if ((SEL4BENCH_EVENT_GENERIC_MASK & event) == SEL4BENCH_EVENT_GENERIC_MASK) {
        uint32_t dummy = 0;
        ia32_cpuid_model_info_t model_info = { .raw = 0 };
        sel4bench_private_cpuid(IA32_CPUID_LEAF_MODEL, 0, &model_info.raw, &dummy, &dummy, &dummy);

        //we should be a P6
        assert(FAMILY(model_info) == IA32_CPUID_FAMILY_P6);

        uint8_t model = MODEL(model_info);
        event = event & ~SEL4BENCH_EVENT_GENERIC_MASK;

        //Using the model summary on http://www.sandpile.org/x86/cpuid.htm#level_0000_0001h
        //Let's hope it's accurate...
        //We are also pretending Atoms don't exist

        //P3 or PM
        if (model <= 0x0D || model == 0x15) {
            return SEL4BENCH_IA32_P6_EVENTS[event];
        }

        switch (model) {
            //CORE
        case 0x0E:
            return SEL4BENCH_IA32_CORE_EVENTS[event];

            //CORE2
        case 0x0F:
        case 0x16:
        case 0x17:
        case 0x1D:
            return SEL4BENCH_IA32_CORE2_EVENTS[event];

            //NEHALEM
        case 0x1A:
        case 0x1E:
        case 0x1F:
        case 0x2E:
            return SEL4BENCH_IA32_NEHALEM_EVENTS[event];

            //WESTMERE
        case 0x25:
        case 0x2C:
        case 0x2F:
            return SEL4BENCH_IA32_WESTMERE_EVENTS[event];

            //SANDY BRIDGE
        case 0x2A:
        case 0x2D:
            return 0x0000; //TODO

            //IVY BRIDGE
        case 0x3A:
        case 0x3E:
            return 0x0000; //TODO

            //HASWELL
        case 0x3C:
        case 0x3F:
        case 0x45:
        case 0x46:
            return SEL4BENCH_IA32_HASWELL_EVENTS[event];

            //BROADWELL
        case 0x3D:
        case 0x47:
        case 0x4F:
        case 0x56:
            return SEL4BENCH_IA32_BROADWELL_EVENTS[event];

            //SKYLAKE
        case 0x4E:
        case 0x5E:
            return SEL4BENCH_IA32_SKYLAKE_EVENTS[event];

            //Unknown
        default:
            return 0x0000;
        }
    } else {
        return event;
    }
}