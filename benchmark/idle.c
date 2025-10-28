/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <sddf/benchmark/sel4bench.h>
#include <sddf/benchmark/bench.h>
#include <sddf/benchmark/config.h>

#define MAGIC_CYCLES 150

__attribute__((__section__(".benchmark_config"))) benchmark_idle_config_t config;

struct bench *b;

static inline uint64_t read_cycle_count() {
    uint64_t cycle_count;
#if CONFIG_ARCH_ARM
    SEL4BENCH_READ_CCNT(cycle_count);
#elif CONFIG_ARCH_RISCV
    asm volatile("rdcycle %0" :"=r"(cycle_count));
#else
#error "unsupported architecture for 'read_cycle_count'"
#endif

    return cycle_count;
}

void count_idle(void)
{
#if ENABLE_BENCHMARKING
    uint64_t val = read_cycle_count();
    b->prev = val;
    b->ccount = 0;

    while (1) {
        val = read_cycle_count();
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
    if (ch == config.init_channel) {
        count_idle();
    } else {
        sddf_dprintf("Idle thread notified on unexpected channel: %u\n", ch);
    }
}

void init(void)
{
    b = (void *)config.cycle_counters;
    return;
}
