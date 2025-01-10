/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/benchmark/sel4bench.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <sddf/benchmark/bench.h>
#include <sddf/benchmark/config.h>

#define MAGIC_CYCLES 150

__attribute__((__section__(".benchmark_config"))) benchmark_idle_config_t config;

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
