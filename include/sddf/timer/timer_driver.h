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

#define F_NANOSECOND     (NS_IN_S)  // equivalent shift frequency for nanoseconds

// Mult-shift cache
typedef struct ms_cache_entry {
    sddf_timer_freq_hz_t f_a;
    sddf_timer_freq_hz_t f_b;
    uint64_t mult;
    uint64_t shift;
} ms_cache_entry_t;

// defined per-driver
/**
 * Set the next timestamp to fire a notification for.
 * Return true on success, or false otherwise.
 */
bool set_new_timeout(uint64_t timestamp);
uint64_t get_current_time(void);

// driver-virt interaction (timer_driver_virt.c)
// This offers a common protected() endpoint and manages
// the "current" time page between the virt and driver.
void set_shared_time_page(uint64_t curr_time);

// time_conv.c
uint64_t do_freq_shift(uint64_t t_a, uint64_t mult, uint64_t shift);
void find_mult_shift(sddf_timer_freq_hz_t f_a, sddf_timer_freq_hz_t f_b, uint64_t *f_mult, uint64_t *f_shift);
sddf_timer_freq_hz_t find_true_freq(sddf_timer_freq_hz_t f, uint64_t prescaler);

// Methods for (nearly) universal common driver -> timer_common.c.
// These are good enough for almost all drivers, but you may want to replace them for complex
// drivers that perform unusual and frequent prescaler programming to avoid
// their most-recently-used cache.
uint64_t tick_to_ns_cached(uint64_t ticks, uint64_t prescaler, sddf_timer_freq_hz_t base_freq);
uint64_t ns_to_tick_cached(uint64_t ns, uint64_t prescaler, sddf_timer_freq_hz_t base_freq);

