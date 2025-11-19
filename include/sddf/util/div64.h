/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Copyright (C) 2003 Bernardo Innocenti <bernie@develer.com>
 * Based on former asm-ppc/div64.h and asm-m68knommu/div64.h
 *
 * Optimization for constant divisors on 32-bit machines:
 * Copyright (C) 2006-2015 Nicolas Pitre
 *
 * The semantics of do_div() is, in C++ notation, observing that the name
 * is a function-like macro and the n parameter has the semantics of a C++
 * reference:
 *
 * uint32_t do_div(uint64_t &n, uint32_t base)
 * {
 * 	uint32_t remainder = n % base;
 * 	n = n / base;
 * 	return remainder;
 * }
 *
 * NOTE: macro parameter n is evaluated multiple times,
 *       beware of side effects!
 */

/*
 * This file implements unsigned 64 bit division consistently between
 * platforms. This is heavily based upon the matching Linux div64 implementation.
 */

#include <sddf/util/fls64.h>
#include <sddf/util/fls.h>
#include <sddf/util/__fls.h>
#include <sddf/util/log2.h>

#if BITS_PER_LONG == 64
/**
 * do_div - returns 2 values: calculate remainder and update new dividend
 * @n: uint64_t dividend (will be updated)
 * @base: uint32_t divisor
 *
 * Summary:
 * ``uint32_t remainder = n % base;``
 * ``n = n / base;``
 *
 * Return: (uint32_t)remainder
 *
 * NOTE: macro parameter @n is evaluated multiple times,
 * beware of side effects!
 */
# define do_div(n,base) ({					\
	uint32_t __base = (base);				\
	uint32_t __rem;						\
	__rem = ((uint64_t)(n)) % __base;			\
	(n) = ((uint64_t)(n)) / __base;				\
	__rem;							\
 })

#elif BITS_PER_LONG == 32


/*
 * If the divisor happens to be constant, we determine the appropriate
 * inverse at compile time to turn the division into a few inline
 * multiplications which ought to be much faster.
 *
 * (It is unfortunate that gcc doesn't perform all this internally.)
 */

#define __div64_const32(n, ___b)					\
({									\
	/*								\
	 * Multiplication by reciprocal of b: n / b = n * (p / b) / p	\
	 *								\
	 * We rely on the fact that most of this code gets optimized	\
	 * away at compile time due to constant propagation and only	\
	 * a few multiplication instructions should remain.		\
	 * Hence this monstrous macro (static inline doesn't always	\
	 * do the trick here).						\
	 */								\
	uint64_t ___res, ___x, ___t, ___m, ___n = (n);			\
	uint32_t ___p;							\
	bool ___bias = false;						\
									\
	/* determine MSB of b */					\
	___p = 1 << ilog2(___b);					\
									\
	/* compute m = ((p << 64) + b - 1) / b */			\
	___m = (~0ULL / ___b) * ___p;					\
	___m += (((~0ULL % ___b + 1) * ___p) + ___b - 1) / ___b;	\
									\
	/* one less than the dividend with highest result */		\
	___x = ~0ULL / ___b * ___b - 1;					\
									\
	/* test our ___m with res = m * x / (p << 64) */		\
	___res = (___m & 0xffffffff) * (___x & 0xffffffff);		\
	___t = (___m & 0xffffffff) * (___x >> 32) + (___res >> 32);	\
	___res = (___m >> 32) * (___x >> 32) + (___t >> 32);		\
	___t = (___m >> 32) * (___x & 0xffffffff) + (___t & 0xffffffff);\
	___res = (___res + (___t >> 32)) / ___p;			\
									\
	/* Now validate what we've got. */				\
	if (___res != ___x / ___b) {					\
		/*							\
		 * We can't get away without a bias to compensate	\
		 * for bit truncation errors.  To avoid it we'd need an	\
		 * additional bit to represent m which would overflow	\
		 * a 64-bit variable.					\
		 *							\
		 * Instead we do m = p / b and n / b = (n * m + m) / p.	\
		 */							\
		___bias = true;						\
		/* Compute m = (p << 64) / b */				\
		___m = (~0ULL / ___b) * ___p;				\
		___m += ((~0ULL % ___b + 1) * ___p) / ___b;		\
	}								\
									\
	/* Reduce m / p to help avoid overflow handling later. */	\
	___p /= (___m & -___m);						\
	___m /= (___m & -___m);						\
									\
	/*								\
	 * Perform (m_bias + m * n) / (1 << 64).			\
	 * From now on there will be actual runtime code generated.	\
	 */								\
	___res = __arch_xprod_64(___m, ___n, ___bias);			\
									\
	___res /= ___p;							\
})

#else
#error "BITS_PER_LONG must be defined as either 32 or 64!"
#endif
