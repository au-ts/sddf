/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

/*
 * Return the current architecture counter value.
 *
 * Each implementation aims to use the required serialisation instructions to ensure
 * an accurate counter read is returned. The ARM barriers try to reflect the x86 synchronisation
 * and the risc-v is the mapping of the ARM barriers from https://docs.riscv.org/reference/isa/unpriv/mm-eplan.html#armmappings
 */
uint64_t sddf_read_counter(void);

/**
 * Return the current architecture counter frequency.
 *
 * Returns a nonzero frequency iff the counter is a trustworthy, invariant
 * clocksource with detectable frequency, or 0 otherwise.
 */
uint64_t sddf_read_freq(void);

#if defined(CONFIG_ARCH_RISCV)
#define COUNTER_UTIL_MAGIC_LEN 5
static char COUNTER_UTIL_MAGIC[COUNTER_UTIL_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x4 };
typedef struct riscv_timestamp_counter_config {
    char magic[COUNTER_UTIL_MAGIC_LEN];
    uint64_t frequency;
} riscv_timestamp_counter_config_t;
#endif
