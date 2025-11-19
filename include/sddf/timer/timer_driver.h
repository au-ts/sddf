/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

// #define DEBUG_TIMER_DRIVER
#ifdef DEBUG_TIMER_DRIVER
#define LOG_TIMER_DRIVER(...) do{ sddf_dprintf("TIMER DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_TIMER_DRIVER(...) do{}while(0)
#endif

#define LOG_TIMER_DRIVER_ERR(...) do{ sddf_dprintf("TIMER DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

uint64_t ticks_to_ns(uint64_t ticks, sddf_timer_freq_hz_t freq);
uint64_t ns_to_ticks(uint64_t ns, sddf_timer_freq_hz_t freq);
uint64_t ticks_to_ns_prescaled(uint64_t ticks, uint64_t prescaler, sddf_timer_freq_hz_t freq);
uint64_t ns_to_ticks_prescaled(uint64_t ns, uint64_t prescaler, sddf_timer_freq_hz_t freq);
