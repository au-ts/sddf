/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/div64.h>

#define MAX_SANE_FREQ_HZ (1 << 30)  // ~1GHz ... nothing should be close to this!
#define F_NANOSECOND     (NS_IN_S)  // equivalent shift frequency for nanoseconds

// Mult-shift cache. It's relatively expensive to calculate this every time, so we just
// don't. Usually we will just be reusing the last result, so we just remember the last
// one. We keep a separate entry for tick->ns and ns->tick.
ms_cache_entry_t tick_to_ns_cache = {0};
ms_cache_entry_t ns_to_tick_cache = {0};

/**
 *  Given two equivalent periods, do a frequency shift calculation.
 *  (equivalent = prescaler-equivalent frequency)
 */
static inline uint64_t do_cached_period_freq_shift(uint64_t t_a, sddf_timer_freq_hz_t f_a,
                                                   sddf_timer_freq_hz_t f_b,
                                                   ms_cache_entry_t *cache_entry)
{
    uint64_t mult, shift = 0;
    // Check cache
    if (cache_entry->f_a == f_a && cache_entry->f_b == f_b) {
        mult = cache_entry->mult;
        shift = cache_entry->shift;
        LOG_TIMER_DRIVER("Used cache for f_a = %u, f_b = %u!\n", f_a, f_b);
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

static inline sddf_timer_freq_hz_t find_true_freq(sddf_timer_freq_hz_t f, uint64_t prescaler)
{
    // TODO: check prescaler handling is sane
    sddf_timer_freq_hz_t true_frequency = f / (1 << (sddf_timer_freq_hz_t)prescaler);
    LOG_TIMER_DRIVER("Prescaler %zu maps %u MHz to equivalent freq of %u\n", prescaler,
                     f, true_frequency / MEGA);
    return true_frequency;
}

/**
 * Given two frequencies, return the integer arithmetic optimised multiplier
 * and shift for the conversion. This uses the method from
 * clocks_calc_mult_shift in the Linux kernel.
 *
 * This function will always try find a conversion that's suitable for the
 * largest range we can fit in 32 bits (~136 years). If you need a longer
 * running clock you should use an alternate method suitable for >64bit
 * integer arithmetic.
 *
 * NOTE: the input frequencies must be EQUIVALENT frequencies, i.e. prescalers
 * should divide the true clock frequency by 2^n
 */
void find_mult_shift(sddf_timer_freq_hz_t f_a, sddf_timer_freq_hz_t f_b, uint64_t *f_mult, uint64_t *f_shift)
{
    // If frequencies are > 1GHz, just die because this method is no longer sound.
    assert(f_a < MAX_SANE_FREQ_HZ && f_b < MAX_SANE_FREQ_HZ);
    // shift_acc: number of bits used by largest possible ticks value in do_period_freq_shift
    uint64_t shift_acc = 32;
    uint64_t tmp = (uint64_t)(UINT32_MAX * f_a) >> 32;

    // Find the limiting shift factor. I.e. try shift values until
    // we would have destroyed all information in the input.
    while (tmp) {
        tmp >>= 1;
        shift_acc--;
    }
    LOG_TIMER_DRIVER("Found shift accuracy as %zu for f_a=%uMHz\n", shift_acc, f_a / (MEGA));

    // Find mult and shift pair with best accuracy that fits range. Given our range
    // is very large, we basically always want a minimal shift.
    // We try increasingly small shifts until we find one that doesn't destroy information.
    uint64_t shift;
    for (shift = 32; shift > 0; shift--) {
        tmp = (uint64_t)f_b << shift;
        tmp += f_a / 2;
        do_div(tmp, f_a);
        if ((tmp >> shift_acc) == 0) {
            // Found it!
            break;
        }
    }
    LOG_TIMER_DRIVER("M=%zu, S=%zu for f_a=%uMHz\n", tmp, shift, f_a / (MEGA));
    *f_mult = tmp;
    *f_shift = shift;
}

/**
 * Perform a frequency shift to convert t_a periods of the input frequency f_a
 * to t_b periods of the output frequency f_b. Use find_mult_shift to get the
 * appropriate magic numbers for your conversion.
 *
 * Mult and shift collectively encode f_a and f_b.
 */
uint64_t do_freq_shift(uint64_t t_a, uint64_t mult, uint64_t shift) {
    return (t_a * mult) >> shift;
}


/**
 * Convert the tick count of a timer to nanoseconds, given the expected prescaler.
 * Prescaler can be set to 0 to ignore.
 *
 * This function internally caches magic values for the calculation, these are recalculated
 * each time the frequency pair changes. Use do_freq_shift() to avoid caching.
 *
 * Prescaler should be given as an exponent, i.e. prescaler counter counts to 2^N,
 * provide N.
 *
 * @param uint64_t ticks to convert
 * @param uint64_t prescaler exponent
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
 * Prescaler should be given as an exponent, i.e. prescaler counter counts to 2^N,
 * provide N.
 *
 * @param uint64_t ticks to convert
 * @param uint64_t prescaler exponent
 * @returns non-zero on failure.
 */
uint64_t ns_to_tick_cached(uint64_t ns, uint64_t prescaler, sddf_timer_freq_hz_t base_freq) {
    sddf_timer_freq_hz_t true_freq = find_true_freq(base_freq, prescaler);
    uint64_t ticks = do_cached_period_freq_shift(ns, F_NANOSECOND, true_freq, &ns_to_tick_cache);
    return ticks;
}


