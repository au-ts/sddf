/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/timer/config.h>
#include <sddf/util/util.h>

// Time conversion functions
#define ONE_GHZ ((sddf_timer_freq_hz_t) (1ULL * GIGA))

/*
 * Compute the effective timer frequency after applying a prescaler.
 *
 * Given a base timer clock frequency `f` and a prescaler selection,
 * returns the frequency at which the timer actually advances.
 *
 * Prescaler values are encoded as the exponent of a power-of-2 divider
 * (i.e., prescaler = 0 -> /1, prescaler = 1 -> /2, prescaler = 2 -> /4, etc.).
 * This matches how prescalers are typically configured in timer hardware:
 * the prescaler register selects the divider by storing log2(divider),
 * and the timer increments at f / 2^prescaler Hz.
 *
 * The prescaler divides the incoming clock to make the timer run slower,
 * trading resolution for a longer maximum count range before overflow.
 */
static inline sddf_timer_freq_hz_t find_true_freq(sddf_timer_freq_hz_t f, uint64_t prescaler)
{
    sddf_timer_freq_hz_t true_frequency = f / (1 << (sddf_timer_freq_hz_t)prescaler);
    return true_frequency;
}

/**
 *  Transform some number of periods in `input_freq` to some number of periods in `target_freq`,
 *  taking extra care to avoid integer division precision loss when dividing the period.
 *
 *  This function will return a transformed number of ticks for any input values that possibly
 *  correspond to 64-bit output for any clock frequency we expect from timers.
 *  See `timer_common.z3` for a proof of correctness.
 *  TODO: return an error if overflow.
 */
static inline uint64_t period_transform(uint64_t period, uint64_t target_freq, uint64_t input_freq)
{
    // We use a split-remainder technique to divide and multiply the `period` without
    // any overflow until `period` is very large.
    // See https://gist.github.com/midnightveil/23fc4dc16cad52114a94fb1978550a98
    uint64_t out_period_whole = (period / input_freq) * target_freq;
    uint64_t period_remainder = period % input_freq;
    uint64_t out_period_remainder = (period_remainder * target_freq) / input_freq;
    return out_period_whole + out_period_remainder;
}

/**
 * These conversion functions are for converting the number of periods (T_a) in some frequency
 * f_a to periods (T_b) of some frequency f_b.
 *
 * That is: T_b = (T_a * f_b) / f_a
 *
 * To convert ticks @ frequency f_a to nanoseconds, we consider output frequency f_b to be
 * 1GHz (or NS_IN_S, same thing!) as one period @ 1GHz is 1ns.
 * -> the number of ticks is the number of nanoseconds
 *
 * So: ns = (ticks * 1GHz) / f_timer
 *
 * To convert from nanoseconds to ticks, are just performing a period shift in the
 * opposite direction ... so `ticks` becomes our number of nanoseconds, our input
 * frequency `f_b` becomes 1GHz, and our output frequency becomes the timer clock freq.
 *
 * So: ticks = (ns * f_timer) / 1GHz
 */

/**
 *  Convert some number of `ticks` @ `freq` to nanoseconds.
 */
uint64_t ticks_to_ns(uint64_t ticks, sddf_timer_freq_hz_t freq)
{
    return period_transform(ticks, ONE_GHZ, freq);
}

/**
 *  Convert a time in `ns` to ticks @ `freq`.
 */
uint64_t ns_to_ticks(uint64_t ns, sddf_timer_freq_hz_t freq)
{
    return period_transform(ns, freq, ONE_GHZ);
}

// Convenience functions for timers using prescalers

/**
 *  Convert a time in `ns` to ticks @ `freq`, with a log2 prescaler value (like typically
 *  used by hardware when setting prescaler regs). See `timer_common.c:find_true_freq` for more
 *  details.
 */
uint64_t ticks_to_ns_prescaled(uint64_t ticks, uint64_t prescaler, sddf_timer_freq_hz_t freq)
{
    sddf_timer_freq_hz_t true_freq = find_true_freq(freq, prescaler);
    return ticks_to_ns(ticks, true_freq);
}

/**
 *  Convert a time in `ns` to ticks @ `freq`, with a log2 prescaler value (like typically
 *  used by hardware when setting prescaler regs). See `timer_common.c:find_true_freq` for more
 *  details.
 */
uint64_t ns_to_ticks_prescaled(uint64_t ns, uint64_t prescaler, sddf_timer_freq_hz_t freq)
{
    sddf_timer_freq_hz_t true_freq = find_true_freq(freq, prescaler);
    return ns_to_ticks(ns, true_freq);
}
