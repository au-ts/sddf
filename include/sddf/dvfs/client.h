/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stddef.h>
#include <stdint.h>
#include <os/sddf.h>

typedef struct {
    uint64_t freq_hz;
    uint64_t voltage_uv;
    uint64_t latency_ns;
} OppEntry;

typedef struct {
    uint64_t core_ident;
    uint64_t clock_source_ident;
    const OppEntry *opptable;
    size_t opptable_len;
} CoreInfo;

#ifdef CONFIG_PLAT_ZYNQMP_ZCU102
const OppEntry OPP_TABLE[] = {
    { .freq_hz = 1199999988, .voltage_uv = 1000000, .latency_ns = 500000 },
    { .freq_hz = 599999994, .voltage_uv = 1000000, .latency_ns = 500000 },
    { .freq_hz = 399999996, .voltage_uv = 1000000, .latency_ns = 500000 },
    { .freq_hz = 299999997, .voltage_uv = 1000000, .latency_ns = 500000 },
};

const size_t OPP_TABLE_LEN = sizeof(OPP_TABLE) / sizeof(OPP_TABLE[0]);

const CoreInfo CPU_INFO[] = {
    { .core_ident = 0, .clock_source_ident = 0, .opptable = OPP_TABLE, .opptable_len = OPP_TABLE_LEN },
    { .core_ident = 1, .clock_source_ident = 0, .opptable = OPP_TABLE, .opptable_len = OPP_TABLE_LEN },
    { .core_ident = 2, .clock_source_ident = 0, .opptable = OPP_TABLE, .opptable_len = OPP_TABLE_LEN },
    { .core_ident = 3, .clock_source_ident = 0, .opptable = OPP_TABLE, .opptable_len = OPP_TABLE_LEN },
};

const size_t CPU_INFO_LEN = sizeof(CPU_INFO) / sizeof(CPU_INFO[0]);
#endif

#define SDDF_DVFS_GET_FREQ 0
#define SDDF_DVFS_SET_FREQ 1

static inline int32_t get_freq(unsigned int channel, uint64_t core_ident, uint32_t *freq)
{
    sddf_set_mr(0, core_ident);

    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_DVFS_GET_FREQ, 0, 0, 1));

    uint32_t error = sddf_get_mr(0);
    if (!error) {
        *freq = sddf_get_mr(1);
    }
    return error;
}

static inline int32_t set_freq(unsigned int channel, uint64_t core_ident, uint32_t freq)
{
    sddf_set_mr(0, core_ident);
    sddf_set_mr(1, freq);

    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_DVFS_SET_FREQ, 0, 0, 2));

    return sddf_get_mr(0);
}