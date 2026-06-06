/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>

#if defined(CONFIG_ARCH_X86)

uint64_t read_counter(void);
uint64_t read_freq(void);

#elif defined(CONFIG_ARCH_AARCH64)

uint64_t read_counter(void);
uint64_t read_freq(void);

#elif defined(CONFIG_ARCH_RISCV)

#error RISC-V timer access not implemented
#endif
