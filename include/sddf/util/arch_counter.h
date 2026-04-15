/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

#if defined(CONFIG_ARCH_X86)
bool is_intel_cpu(void);
/* On intel x86 if the TSC is not invariant then if the processor is put into sleep states or is overclocked then the
 * result of reading it may be invalid.
 */
bool is_invariant_tsc(void);
#endif //x86 specific helper functions

/*
 * Return the current architecture counter value.
 *
 * Each implementation aims to use the required serialisation instructions to ensure
 * an accurate counter read is returned. The ARM barriers try to reflect the x86 synchronisation
 * and the risc-v is the mapping of the ARM barriers from https://docs.riscv.org/reference/isa/unpriv/mm-eplan.html#armmappings
 */
uint64_t read_counter(void);
/* This may return 0 if frequency was not available */
uint64_t read_freq(void);

#if defined(CONFIG_ARCH_RISCV)
#define COUNTER_UTIL_MAGIC_LEN 5
static char COUNTER_UTIL_MAGIC[COUNTER_UTIL_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x4 };
typedef struct arch_counter_config {
    char magic[COUNTER_UTIL_MAGIC_LEN];
    uint64_t frequency;
} arch_counter_config_t;
#endif
