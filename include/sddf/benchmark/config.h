/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <os/sddf.h>
#include <stdint.h>
#include <stdbool.h>

#define BENCHMARK_MAX_CHILDREN 64 // TODO: Can we have a higher upper bound on this?
#define BENCHMARK_MAX_CORES 64

typedef struct benchmark_child_config {
    char name[SDDF_NAME_LENGTH];
    uint8_t child_id;
} benchmark_child_config_t;

typedef struct benchmark_config {
    uint8_t rx_start_ch;
    uint8_t tx_start_ch;
    uint8_t rx_stop_ch;
    uint8_t tx_stop_ch;
    uint8_t init_ch;
    uint8_t core;
    bool last_core;
    uint8_t num_children;
    benchmark_child_config_t children[BENCHMARK_MAX_CHILDREN];
} benchmark_config_t;

typedef struct benchmark_idle_config {
    void *cycle_counters;
    uint8_t init_channel;
} benchmark_idle_config_t;

typedef struct benchmark_client_config {
    uint8_t start_ch;
    uint8_t stop_ch;
    uint8_t num_cores;
    void *core_ccounts[BENCHMARK_MAX_CORES];
} benchmark_client_config_t;
