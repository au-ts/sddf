/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <os/sddf.h>
#include <stdint.h>
#include <stdbool.h>

/* At the moment we run systems that contain this benchmarking code on architectures
 * where we cannot properly do benchmarking. We also include the benchmarking PD
 * on non-benchmarking configurations.
 * This defines whether we actually try to benchmark, setup the PMU etc.
 */
#if defined(CONFIG_ENABLE_BENCHMARKS) && (defined(CONFIG_ARCH_ARM) || defined(CONFIG_ARCH_RISCV))
#define ENABLE_BENCHMARKING 1
#else
#define ENABLE_BENCHMARKING 0
#endif

/* While we can get cycle count and utilisation results on RISC-V, we cannot yet get
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
    /* Initialisation channel shared with the idle thread on the same core. */
    uint8_t init_ch;
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
} benchmark_config_t;

typedef struct benchmark_idle_config {
    /* Address to store the core's cycle counts. Shared with the benchmarking
    client PD. */
    void *cycle_counters;
    /* Initialisation channel shared with the benchmark PD on the same core. */
    uint8_t init_channel;
} benchmark_idle_config_t;

typedef struct benchmark_client_config {
    /* Channel to notify the first benchmark PD that a benchmark has started.
    Each benchmark PD propagates this notification to the benchmark PD on the
    next core. */
    uint8_t start_ch;
    /* Channel to notify the first benchmark PD that a benchmark has finished.
    Each benchmark PD propagates this notification to the benchmark PD on the
    next core. */
    uint8_t stop_ch;
    /* Number of active cores in the system. */
    uint8_t num_cores;
    /* Addresses of each active core's cycle counts maintained by and shared
    with the idle thread on that core. */
    void *core_ccounts[CONFIG_MAX_NUM_NODES];
} benchmark_client_config_t;
