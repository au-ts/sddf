/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#define MASK(width)  ((1UL << width) - 1)

#define abs(x) ( ( (x) < 0) ? -(x) : (x) )

#define DIV_ROUND_UP(n, d) (((n) + (d) - 1) / (d))

#define do_div(n, base) ({                              \
    uint32_t __base = (base);                           \
    uint32_t __rem;                                     \
    __rem = ((uint64_t)(n)) % __base;                   \
    (n) = ((uint64_t)(n)) / __base;                     \
    __rem;                                              \
 })

#define DIV_ROUND_DOWN_ULL(ll, d)                       \
    ({ uint64_t _tmp = (ll); do_div(_tmp, d); _tmp; })

#define DIV_ROUND_UP_ULL(ll, d)                         \
    DIV_ROUND_DOWN_ULL((uint64_t)(ll) + (d) - 1, (d))

#define DIV_ROUND_CLOSEST_ULL(x, divisor)(              \
{                                                       \
    typeof(divisor) __d = divisor;                      \
    unsigned long long _tmp = (x) + (__d) / 2;          \
    do_div(_tmp, __d);                                  \
    _tmp;                                               \
}                                                       \
)
