/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

/* Prevent the compiler from re-ordering any read or write across the fence. */
#define COMPILER_MEMORY_FENCE() __atomic_signal_fence(__ATOMIC_ACQ_REL)

/* Prevent the compiler from re-ordering any write which follows the fence
 * in program order with any read or write which preceeds the fence in
 * program order. */
#define COMPILER_MEMORY_RELEASE() __atomic_signal_fence(__ATOMIC_RELEASE)

/* Prevent the compiler from re-ordering any read which preceeds the fence
 * in program order with any read or write which follows the fence in
 * program order. */
#define COMPILER_MEMORY_ACQUIRE() __atomic_signal_fence(__ATOMIC_ACQUIRE)

/* THREAD_MEMORY_FENCE: Implements a full processor memory barrier.
 * All stores before this point are completed, and all loads after this
 * point are delayed until after it.
 */
#define THREAD_MEMORY_FENCE() __atomic_thread_fence(__ATOMIC_ACQ_REL)

/* THREAD_MEMORY_RELEASE: Implements a fence which has the effect of
 * forcing all stores before this point to complete.
 */
#define THREAD_MEMORY_RELEASE() __atomic_thread_fence(__ATOMIC_RELEASE)

/* THREAD_MEMORY_ACQUIRE: Implements a fence which has the effect of
 * forcing all loads beyond this point to occur after this point.
 */
#define THREAD_MEMORY_ACQUIRE() __atomic_thread_fence(__ATOMIC_ACQUIRE)

/* load_acquire_32: synchronises with a store_release_32 that writes the same value to the same location
 */
static inline uint32_t load_acquire_32(const uint32_t *ptr)
{
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    return __atomic_load_n(ptr, __ATOMIC_ACQUIRE);
#else
    uint32_t ret = __atomic_load_n(ptr, __ATOMIC_RELAXED);
    __atomic_signal_fence(__ATOMIC_ACQUIRE);
    return ret;
#endif
}

/* store_release_32: synchronises with a load_acquire_32 to the same location
 */
static inline void store_release_32(uint32_t *ptr, uint32_t value)
{
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    __atomic_store_n(ptr, value, __ATOMIC_RELEASE);
#else
    __atomic_signal_fence(__ATOMIC_RELEASE);
    __atomic_store_n(ptr, value, __ATOMIC_RELAXED);
#endif
}

static inline uint32_t load_relaxed_32(const uint32_t *ptr)
{
    return __atomic_load_n(ptr, __ATOMIC_RELAXED);
}

/* load_acquire_16: synchronises with a store_release_16 that writes the same value to the same location
 */
static inline uint16_t load_acquire_16(const uint16_t *ptr)
{
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    return __atomic_load_n(ptr, __ATOMIC_ACQUIRE);
#else
    uint16_t ret = __atomic_load_n(ptr, __ATOMIC_RELAXED);
    __atomic_signal_fence(__ATOMIC_ACQUIRE);
    return ret;
#endif
}

/* store_release_16: synchronises with a load_acquire_16 to the same location
 */
static inline void store_release_16(uint16_t *ptr, uint16_t value)
{
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    __atomic_store_n(ptr, value, __ATOMIC_RELEASE);
#else
    __atomic_signal_fence(__ATOMIC_RELEASE);
    __atomic_store_n(ptr, value, __ATOMIC_RELAXED);
#endif
}

static inline uint16_t load_relaxed_16(const uint16_t *ptr)
{
    return __atomic_load_n(ptr, __ATOMIC_RELAXED);
}
