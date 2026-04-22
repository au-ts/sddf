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
bool is_invariant_tsc(void);
#endif //x86 specific helper functions

uint64_t read_counter(void);
/* This may return 0 if frequency was not available on x86 */
uint64_t read_freq(void);
