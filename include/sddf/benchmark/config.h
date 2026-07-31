/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <os/sddf.h>
#include <stdint.h>
#include <stdbool.h>
#include "bench.h"

/*
 * This defines whether we actually try to benchmark.
 * If the PMU is available that will be enabled below.
 */
#if defined(CONFIG_ENABLE_BENCHMARKS)
#define ENABLE_BENCHMARKING 1
#else
#define ENABLE_BENCHMARKING 0
#endif

/* While we can get cycle count and utilisation results on RISC-V and x86, we cannot yet get
 * PMU event information (cache misses, instruction counts etc) */
#if defined(CONFIG_ENABLE_BENCHMARKS) && defined(CONFIG_ARCH_ARM)
#define ENABLE_PMU_EVENTS 1
#else
#define ENABLE_PMU_EVENTS 0
#endif

#define BENCHMARK_MAX_CHILDREN 64 // TODO: Can we have a higher upper bound on this?

typedef struct benchmark_child_config {
    char name[SDDF_NAME_LENGTH];
    uint8_t child_id;
} benchmark_child_config_t;

typedef struct benchmark_config {
    /* Channel a benchmark PD receives the benchmark start notification on. */
    uint8_t rx_start_ch;
    /* Channel a benchmark PD transmits the benchmark start notification on
    (start signal is propagated to benchmark PDs on each core). */
    uint8_t tx_start_ch;
    /* Channel a benchmark PD receives the benchmark stop notification on. */
    uint8_t rx_stop_ch;
    /* Channel a benchmark PD transmits the benchmark stop notification on
    (stop signal is propagated to benchmark PDs on each core). */
    uint8_t tx_stop_ch;
    /* Core a benchmark PD resides on. Used for displaying benchmark results. */
    uint8_t core;
    /* Whether a benchmark PD is on the last core to receive start and stop
    signals. If last_core is set to true, the above tx channels are invalid. */
    bool last_core;
    /* Number of PDs requiring cycle counts sharing a core with this benchmark
    PD. */
    uint8_t num_children;
    /* PDs requiring cycle counts sharing a core with this benchmark PD. */
    benchmark_child_config_t children[BENCHMARK_MAX_CHILDREN];
    /* PMU events to track */
    uint8_t pmu_events[BENCHMARK_MAX_PMU_EVENTS];
    /* Number of PMU events to track */
    uint8_t num_pmu_events;
} benchmark_config_t;

typedef struct benchmark_client_config {
    /* Channel to notify the first benchmark PD that a benchmark has started.
    Each benchmark PD propagates this notification to the benchmark PD on the
    next core. */
    uint8_t start_ch;
    /* Channel to notify the first benchmark PD that a benchmark has finished.
    Each benchmark PD propagates this notification to the benchmark PD on the
    next core. */
    uint8_t stop_ch;
    /* Flag set to true if this is the benchmark controller. */
    uint8_t is_benchmark_controller;
} benchmark_client_config_t;
