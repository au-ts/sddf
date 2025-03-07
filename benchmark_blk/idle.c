/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/benchmark/sel4bench.h>
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
    uint64_t val;
    SEL4BENCH_READ_CCNT(val);
    b->ccount = 0;

    /*
     * NOTE: for block benchmarking, the idle thread is only used as a "busy loop" sitting as a child
     * PD of the `bench` PD, so its PMU cycle counter gets incremented when the CPU is idle. For that purpose,
     * the PD running the idle.elf binary should have the LOWEST possible priority, so it is only scheduled when 
     * driver, virtualiser and the client have nothing to  do (e.g. waiting for I/O).
     */
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
    if (ch == config.init_channel) {
        count_idle();
    } else {
        sddf_dprintf("Idle thread notified on unexpected channel: %u\n", ch);
    }
}

void init(void)
{
    b = (void *)config.cycle_counters;
    sddf_printf("IDLE| idle thread starting\n");
    return;
}
