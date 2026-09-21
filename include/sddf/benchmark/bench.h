/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/**
 * On the ARM CPUs we use, there are 6 32-bit counters available for tracking
 * PMU events. PMU events can be selected using the BENCH_PMU_EVENTS make flag
 * or in the metaprogram. The selected events are serialised and copied into the
 * benchmark PD's ELF file.
 */
#define BENCHMARK_MAX_PMU_EVENTS 6
