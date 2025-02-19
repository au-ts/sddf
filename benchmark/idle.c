/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/benchmark/sel4bench.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <sddf/benchmark/bench.h>

#define INIT 3
#define MAGIC_CYCLES 150

uintptr_t cyclecounters_vaddr;
struct bench *b;

void count_idle(void)
{
    #ifdef MICROKIT_CONFIG_benchmark
    uint64_t val;
    SEL4BENCH_READ_CCNT(val);
    b->prev = val;
    b->ccount = 0;

    while (1) {
        SEL4BENCH_READ_CCNT(val);
        __atomic_store_n(&b->ts, val, __ATOMIC_RELAXED);
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