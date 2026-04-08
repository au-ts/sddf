/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>

sddf_timer_freq_hz_t find_true_freq(sddf_timer_freq_hz_t f, uint64_t prescaler)
{
    sddf_timer_freq_hz_t true_frequency = f / (1 << (sddf_timer_freq_hz_t)prescaler);
    return true_frequency;
}

/**
 * Given two frequencies, return the integer arithmetic optimised multiplier
 * and shift for the conversion. This uses the method from
 * clocks_calc_mult_shift in the Linux kernel.
 *
 * NOTE: the input frequencies must be EQUIVALENT frequencies, i.e. prescalers
 * should divide the true clock frequency by 2^n
 */
void find_mult_shift(sddf_timer_freq_hz_t f_a, sddf_timer_freq_hz_t f_b, uint64_t *f_mult, uint64_t *f_shift)
{
    // shift_acc: number of bits used by largest possible ticks value in do_period_freq_shift
    uint64_t shift_acc = 32;
    uint64_t tmp = ((uint64_t)UINT32_MAX * (uint64_t)f_a) >> 32;

    LOG_TIMER_DRIVER("tmp=%zu\n", tmp);
    // Find the limiting shift factor. I.e. try shift values until
    // we would have destroyed all information in the input.
    while (tmp) {
        tmp >>= 1;
        shift_acc--;
    }

    // Find mult and shift pair with best accuracy that fits range.
    // We try increasingly small shifts until we find one that doesn't destroy information.
    uint64_t shift;
    for (shift = 32; shift > 0; shift--) {
        tmp = (uint64_t)f_b << shift;
        tmp += (uint64_t)f_a / 2ULL;
        tmp /= (uint64_t)f_a;
        if ((tmp >> shift_acc) == 0) {
            break; // Found it!
        }
    }
    LOG_TIMER_DRIVER("M=%zu, S=%zu, S_A=%zu for f_a=%uMHz\n", tmp, shift, shift_acc, f_a / (MEGA));

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
     // __uint128_t multiplicand = (__uint128_t)t_a * (__uint128_t)mult;
    uint64_t multiplicand = t_a * mult;
    return (uint64_t) (multiplicand >> shift);
}
