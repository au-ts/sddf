/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <sddf/util/printf.h>
#include <sddf/dvfs/protocol.h>

#define DEBUG_DVFS_DRIVER
#ifdef DEBUG_DVFS_DRIVER
#define LOG_DVFS_DRIVER(...) do{ sddf_dprintf("DVFS DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DVFS_DRIVER(...) do{}while(0)
#endif

#define LOG_DVFS_DRIVER_ERR(...) do{ sddf_dprintf("DVFS DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)


typedef struct op_point {
    uint64_t freq_hz;
    uint64_t voltage_uv;
    uint64_t latency_ns;    // NOTE: this is dead code?
} dvfs_op_point_t;

// TODO: figure out a way to make clk_src_id somehow more true to DTS.
typedef struct dvfs_core_info {
    uint64_t core_id;
    uint64_t clk_src_id;    // Reference to clock binding for platform.
    uint64_t regulator_id;  // Reference to regulator for core voltage adjustment
    const dvfs_op_point_t *op_point_tbl;  // point to constant array
} dvfs_core_info_t;
// NOTE: op point table should always be the same on a clustser UNLESS hetereogeneous cores.
// NOTE: op point table should be sorted in power order. 0th entry is lowest power state.
