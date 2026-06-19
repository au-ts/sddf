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

static inline uint64_t read_cycle_count()
{
    uint64_t cycle_count;
#if defined(CONFIG_ARCH_ARM)
    SEL4BENCH_READ_CCNT(cycle_count);
#elif defined(CONFIG_ARCH_RISCV)
    asm volatile("rdcycle %0" : "=r"(cycle_count));
#elif defined(CONFIG_ARCH_X86_64)
    // Do nothing only for build atm
#else
#error "read_cycle_count: unsupported architecture"
#endif

    return cycle_count;
}

void count_idle(void)
{
#if ENABLE_BENCHMARKING
    b->prev_ccount = read_cycle_count();

    /*
     * NOTE: for block benchmarking, the idle thread is only used as a "busy loop" sitting as a child
     * PD of the `bench` PD, so its PMU cycle counter gets incremented when the CPU is idle. For that purpose,
     * the PD running the idle.elf binary should have the LOWEST possible priority, so it is only scheduled when 
     * driver, virtualiser and the client have nothing to  do (e.g. waiting for I/O).
     */
    while (1) {
        __atomic_store_n(&b->core_ccount, read_cycle_count(), __ATOMIC_RELAXED);
        uint64_t diff = b->core_ccount - b->prev_ccount;

        if (diff < MAGIC_CYCLES) {
            __atomic_store_n(&b->idle_ccount, __atomic_load_n(&b->idle_ccount, __ATOMIC_RELAXED) + diff,
                             __ATOMIC_RELAXED);
        }

        b->prev_ccount = b->core_ccount;
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
