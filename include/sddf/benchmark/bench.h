/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

/**
 * This benchmarking struct is used to calculate system utilisation in the echo
 * server example. Each core has an idle thread which keeps track of total core
 * cycle count (`core_ccount`), as well as it's own cycle count (`idle_ccount`).
 * The remaining cycles can then be attributed to the system.
 *
 * The idle thread achieves this by reading the core cycle count each time it is
 * scheduled. The new value is then compared to the previously recorded value
 * (`prev_ccount`) to deduce whether the idle thread has been pre-empted between
 * reads. If the difference is sufficiently small, the idle thread assumes it
 * has NOT been pre-empted, and the difference in cycle counts is added to the
 * idle thread's cycle count.
 *
 * These cycle count values are also stored in shared memory with the echo
 * server benchmarking client, who will send them to the ipbench controller upon
 * benchmark completion.
 */
struct bench {
    /* Most recent total core cycle count */
    uint64_t core_ccount;
    /* Previously recorded total core cycle count */
    uint64_t prev_ccount;
    /* Cycles attributed to the idle thread */
    uint64_t idle_ccount;
};

/**
 * On the ARM CPUs we use, there are 6 32-bit counters available for tracking
 * PMU events. PMU events can be selected using the BENCH_PMU_EVENTS make flag
 * or in the metaprogram. The selected events are serialised and copied into the
 * benchmark PD's ELF file.
 */
#define BENCHMARK_MAX_PMU_EVENTS 6

/**
 * PMU event identifiers - used by the metaprogram to select events. Event i is
 * described by the pmu_event_table[i] entry in benchmark.c.
 */
typedef enum {
    CACHE_L1I_MISS = 0,
    CACHE_L1D_MISS,
    TLB_L1I_MISS,
    TLB_L1D_MISS,
    EXECUTE_INSTRUCTION,
    BRANCH_MISPREDICT,
    CPU_CYCLES,
    MEM_ACCESS,
    CHAIN,
    PMU_EVENT_COUNT,
} bench_pmu_events_t;
