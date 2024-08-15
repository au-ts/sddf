/*
 * Copyright LLVM Project
 * SPDX-License-Identifier: LicenseRef-APACHE-2-LLVM-EXCEPTION
 */

//===-- udivmodti4.c - Implement __udivmodti4 -----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
//
//===----------------------------------------------------------------------===//
//
// This file implements __udivmodti4 for the compiler_rt library.
//
//===----------------------------------------------------------------------===//

#pragma once

#include <stdint.h>

#define CHAR_BIT 8

typedef union {
    __uint128_t all;
    struct {
        uint64_t low;
        uint64_t high;
    } s;
} utwords;

// Returns the 128 bit division result by 64 bit. Result must fit in 64 bits.
// Remainder stored in r.
// Taken and adjusted from libdivide libdivide_128_div_64_to_64 division
// fallback. For a correctness proof see the reference for this algorithm
// in Knuth, Volume 2, section 4.3.1, Algorithm D.
static inline uint64_t udiv128by64to64default(uint64_t u1, uint64_t u0, uint64_t v,
                                              uint64_t *r)
{
    const unsigned n_udword_bits = sizeof(uint64_t) * CHAR_BIT;
    const uint64_t b = (1ULL << (n_udword_bits / 2)); // Number base (32 bits)
    uint64_t un1, un0;                                // Norm. dividend LSD's
    uint64_t vn1, vn0;                                // Norm. divisor digits
    uint64_t q1, q0;                                  // Quotient digits
    uint64_t un64, un21, un10;                        // Dividend digit pairs
    uint64_t rhat;                                    // A remainder
    int32_t s;                                       // Shift amount for normalization

    s = __builtin_clzll(v);
    if (s > 0) {
        // Normalize the divisor.
        v = v << s;
        un64 = (u1 << s) | (u0 >> (n_udword_bits - s));
        un10 = u0 << s; // Shift dividend left
    } else {
        // Avoid undefined behavior of (u0 >> 64).
        un64 = u1;
        un10 = u0;
    }

    // Break divisor up into two 32-bit digits.
    vn1 = v >> (n_udword_bits / 2);
    vn0 = v & 0xFFFFFFFF;

    // Break right half of dividend into two digits.
    un1 = un10 >> (n_udword_bits / 2);
    un0 = un10 & 0xFFFFFFFF;

    // Compute the first quotient digit, q1.
    q1 = un64 / vn1;
    rhat = un64 - q1 * vn1;

    // q1 has at most error 2. No more than 2 iterations.
    while (q1 >= b || q1 * vn0 > b * rhat + un1) {
        q1 = q1 - 1;
        rhat = rhat + vn1;
        if (rhat >= b) {
            break;
        }
    }

    un21 = un64 * b + un1 - q1 * v;

    // Compute the second quotient digit.
    q0 = un21 / vn1;
    rhat = un21 - q0 * vn1;

    // q0 has at most error 2. No more than 2 iterations.
    while (q0 >= b || q0 * vn0 > b * rhat + un0) {
        q0 = q0 - 1;
        rhat = rhat + vn1;
        if (rhat >= b) {
            break;
        }
    }

    *r = (un21 * b + un0 - q0 * v) >> s;
    return q1 * b + q0;
}

static inline uint64_t udiv128by64to64(uint64_t u1, uint64_t u0, uint64_t v,
                                       uint64_t *r)
{

    return udiv128by64to64default(u1, u0, v, r);
}