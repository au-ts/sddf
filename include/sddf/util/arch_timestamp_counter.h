/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

/**
 * Architecture counter accessors.
 *
 * Clients should use sddf_timer_time_now(), which uses these for a local
 * fast-path when the counter is usable and otherwise falls back to a PPC
 * into the timer driver. These raw accessors are exposed so that drivers
 * may also use them.
 */

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
