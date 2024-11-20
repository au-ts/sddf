/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#ifdef CONFIG_ARCH_X86_64
#include <sddf/benchmark/x86/sel4bench.h>
#else 
#include <sddf/benchmark/arm/sel4bench.h>
#endif
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <sddf/benchmark/bench.h>

#define INIT 3
#ifdef CONFIG_ARCH_X86_64
#define MAGIC_CYCLES 150
#else
#define MAGIC_CYCLES 150
#endif

uintptr_t cyclecounters_vaddr = 0x5010000;
struct bench *b;

void count_idle(void)
{
    #ifdef MICROKIT_CONFIG_benchmark
    b->prev = sel4bench_get_cycle_count();
    b->ccount = 0;

    while (1) {
        __atomic_store_n(&b->ts, (uint64_t)sel4bench_get_cycle_count(), __ATOMIC_RELAXED);
        uint64_t diff = b->ts - b->prev;

        if (diff < MAGIC_CYCLES) {
            __atomic_store_n(&b->ccount, __atomic_load_n(&b->ccount, __ATOMIC_RELAXED) + diff, __ATOMIC_RELAXED);
        }

        b->prev = b->ts;
    }
    #endif
}

void notified(microkit_channel ch)
{
    switch(ch) {
        case INIT:
            count_idle();
            break;
        default:
            sddf_dprintf("Idle thread notified on unexpected channel: %u\n", ch);
    }
}

void init(void)
{
    b = (void *)cyclecounters_vaddr;
    return;
}
