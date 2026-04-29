/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>

// This file implements cached time conversion which is suitable for almost
// all timer drivers. Omit this file and use your own time conversion in your driver
// if you do not want the caching behaviour.

ms_cache_entry_t tick_to_ns_cache = { 0 };
ms_cache_entry_t ns_to_tick_cache = { 0 };

/**
 *  Given two equivalent periods, do a frequency shift calculation.
 *  (equivalent = prescaler-equivalent frequency)
 */
static inline uint64_t do_cached_period_freq_shift(uint64_t t_a, sddf_timer_freq_hz_t f_a, sddf_timer_freq_hz_t f_b,
                                                   ms_cache_entry_t *cache_entry)
{
    uint64_t mult, shift = 0;
    // Check cache
    if (cache_entry->f_a == f_a && cache_entry->f_b == f_b) {
        mult = cache_entry->mult;
        shift = cache_entry->shift;
        // LOG_TIMER_DRIVER("Used cache for f_a = %u, f_b = %u!\n", f_a, f_b);
    } else {
        find_mult_shift(f_a, f_b, &mult, &shift);
        // Store result
        cache_entry->mult = mult;
        cache_entry->shift = shift;
        cache_entry->f_a = f_a;
        cache_entry->f_b = f_b;
    }
    return do_freq_shift(t_a, mult, shift);
}

/**
 * Convert the tick count of a timer to nanoseconds, given the expected prescaler.
 * Prescaler can be set to 0 to ignore.
 *
 * This function internally caches magic values for the calculation, these are recalculated
 * each time the frequency pair changes. Use do_freq_shift() to avoid caching.
 *
 * @param uint64_t ticks to convert
 * @param uint64_t prescaler exponent - i.e. if scaling to 2^N give N.
 * @returns non-zero on failure.
 */
uint64_t tick_to_ns_cached(uint64_t ticks, uint64_t prescaler, sddf_timer_freq_hz_t base_freq)
{
    sddf_timer_freq_hz_t true_freq = find_true_freq(base_freq, prescaler);
    // convert to F_NANOSECOND ... a frequency where a period is exactly 1ns.
    // this seems like a hack, but the underlying math to do unit conversions is always
    // a frequency shift!
    uint64_t ns = do_cached_period_freq_shift(ticks, true_freq, F_NANOSECOND, &tick_to_ns_cache);
    return ns;
}

/**
 * Convert the tick count of a timer to nanoseconds, given the expected prescaler.
 * Prescaler can be set to 0 to ignore.
 *
 * This function internally caches magic values for the calculation, these are recalculated
 * each time the frequency pair changes. Use do_freq_shift() to avoid caching.
 *
 * @param uint64_t ticks to convert
 * @param uint64_t prescaler exponent - i.e. if scaling to 2^N give N.
 * @returns non-zero on failure.
 */
uint64_t ns_to_tick_cached(uint64_t ns, uint64_t prescaler, sddf_timer_freq_hz_t base_freq)
{
    sddf_timer_freq_hz_t true_freq = find_true_freq(base_freq, prescaler);
    uint64_t ticks = do_cached_period_freq_shift(ns, F_NANOSECOND, true_freq, &ns_to_tick_cache);
    return ticks;
}
