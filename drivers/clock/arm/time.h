/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

/*
 * Time should use a 64-bit data type, because a 32-bit type can overflow too
 * easily for longer timeouts. However, there are no hard-coded assumptions
 * about this in here. Postfixing values with "lu" or "llu" is configurable to
 * allow aligning this with the runtme library definitions for uint64_t and
 * PRIu64. The macro SEL4_TIME_UINT_TYPE() defaults to UINT64_C(), which is a
 * common way runtime libraries defines 64-bit datatypes:
 *
 *     #if defined(target_is_32_bit_with_LLP64)
 *         typedef unsigned long long int   uint64_t
 *         #define UINT64_C(v)              v ## ull
 *         #define PRIu64                   "ull"
 *
 *     #elif defined(target_is_64_bit_with_LP64)
 *         typedef unsigned long int        uint64_t
 *         #define UINT64_C(v)              v ## ul
 *         #define PRIu64                   "ul"
 *     ...
 *     #endif
 *
 * See also https://en.wikipedia.org/wiki/64-bit_computing for commonly used
 * 64-bit data models. The seL4 kernel uses "long long" for 64-bit types, see
 * file <sel4-kernel>/include/stdint.h. The userspace is not required to follow
 * this, musllibc uses "long long" on 32-bit targets and "long" on 64-bit
 * targets.
 */
#ifndef SEL4_TIME_UINT_TYPE
#define SEL4_TIME_UINT_TYPE(v)  UINT64_C(v)
#endif

/* seconds */
#define SEC_IN_MINUTE   SEL4_TIME_UINT_TYPE(60)

/* milliseconds */
#define MS_IN_S         SEL4_TIME_UINT_TYPE(1000)
#define MS_IN_MINUTE    (MS_IN_S * SEC_IN_MINUTE)   /* =6e4 */

/* microseconds */
#define US_IN_MS        SEL4_TIME_UINT_TYPE(1000)
#define US_IN_S         (US_IN_MS * MS_IN_S)
#define US_IN_MINUTE    (US_IN_MS * MS_IN_MINUTE)   /* =6e7 */

/* nanoseconds */
#define NS_IN_US        SEL4_TIME_UINT_TYPE(1000)
#define NS_IN_MS        (NS_IN_US * US_IN_MS)
#define NS_IN_S         (NS_IN_US * US_IN_S)
#define NS_IN_MINUTE    (NS_IN_US * US_IN_MINUTE)   /* =6e10 > 2^32 (=4e9) */

/* picoseconds */
#define PS_IN_NS        SEL4_TIME_UINT_TYPE(1000)
#define PS_IN_US        (PS_IN_NS * NS_IN_US)
#define PS_IN_MS        (PS_IN_NS * NS_IN_MS)
#define PS_IN_S         (PS_IN_NS * NS_IN_S)        /* =1e12 > 2^32 (=4e9) */
#define PS_IN_MINUTE    (PS_IN_NS * NS_IN_MINUTE)   /* =6e13 > 2^32 (=4e9) */

/* femptoseconds */
#define FS_IN_PS        SEL4_TIME_UINT_TYPE(1000)
#define FS_IN_NS        (FS_IN_PS * PS_IN_NS)
#define FS_IN_US        (FS_IN_PS * PS_IN_US)
#define FS_IN_MS        (FS_IN_PS * PS_IN_MS)       /* =1e12 > 2^32 (=4e9) */
#define FS_IN_S         (FS_IN_PS * PS_IN_S)        /* =1e15 > 2^32 (=4e9) */
#define FS_IN_MINUTE    (FS_IN_PS * PS_IN_MINUTE)   /* =6e16 > 2^32 (=4e9) */

/* Note that the maximum value for uint64_t is 1.8e19. FS_IN_MINUTE is 6e16,
 * which is still in range. There are 1e18 atto-seconds in one second, which
 * eventually gets close to the uint64_t range, the 6e19 atto-seconds in a
 * minute exceed it.
 */
