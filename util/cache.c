/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/util/cache.h>
#include <sddf/util/util.h>

/*
 * This is a small utility library for performing cache operations in order
 * to deal with DMA cache coherency. On DMA coherent architectures/platforms
 * (such as certain RISC-V platforms and x86), these operations are no-ops.
 *
 * This library currently has the assumption that all RISC-V platforms are
 * DMA coherent, it does not support platforms with the Zicbom extension.
 */

#ifdef CONFIG_ARCH_AARCH64

/*
 * On ARM, we perform all cache operations from user-space. We do not have a
 * cache_invalidate as the ARM instruction to do so -- `dc ivac` --
 * is not supported in userspace (EL0). See [1].
 *
 * [1]: https://developer.arm.com/documentation/ddi0595/2021-06/AArch64-Instructions/DC-IVAC--Data-or-unified-Cache-line-Invalidate-by-VA-to-PoC
 */

#ifndef CONFIG_AARCH64_USER_CACHE_ENABLE
#error "CONFIG_AARCH64_USER_CACHE_ENABLE must be enabled"
#error "seL4 must be configured with CONFIG_AARCH64_USER_CACHE_ENABLE"
#endif

#define LINE_INDEX(a) (a >> CONFIG_L1_CACHE_LINE_SIZE_BITS)

#endif

/*
 * Cleans and invalidates the from start to end. This is not inclusive.
 * If end is on a cache line boundary, the cache line starting at end
 * will not be cleaned/invalidated.
 *
 * On ARM, this operation ultimately performs the 'dc civac' instruction.
 * On RISC-V, this is a no-op.
 */
void cache_clean_and_invalidate(unsigned long start, unsigned long end)
{
#ifdef CONFIG_ARCH_AARCH64
    unsigned long vaddr;
    unsigned long index;

    assert(start != end);

    /* If the end address is not on a cache line boundary, we want to perform
     * the cache operation on that cache line as well. */
    unsigned long end_rounded = ROUND_UP(end, 1 << CONFIG_L1_CACHE_LINE_SIZE_BITS);

    for (index = LINE_INDEX(start); index < LINE_INDEX(end_rounded); index++) {
        vaddr = index << CONFIG_L1_CACHE_LINE_SIZE_BITS;
        asm volatile("dc civac, %0" : : "r"(vaddr));
        asm volatile("dsb sy" ::: "memory");
    }
#endif
}

/*
 * Cleans from start to end. This is not inclusive.
 * If end is on a cache line boundary, the cache line starting at end
 * will not be cleanend.
 *
 * On ARM, this operation ultimately performs the 'dc cvac' instruction.
 * On RISC-V, this is a no-op.
 */
void cache_clean(unsigned long start, unsigned long end)
{
#ifdef CONFIG_ARCH_AARCH64
    unsigned long vaddr;
    unsigned long index;

    assert(start != end);

    /* If the end address is not on a cache line boundary, we want to perform
     * the cache operation on that cache line as well. */
    unsigned long end_rounded = ROUND_UP(end, 1 << CONFIG_L1_CACHE_LINE_SIZE_BITS);

    for (index = LINE_INDEX(start); index < LINE_INDEX(end_rounded); index++) {
        vaddr = index << CONFIG_L1_CACHE_LINE_SIZE_BITS;
        asm volatile("dc cvac, %0" : : "r"(vaddr));
        asm volatile("dmb sy" ::: "memory");
    }
#endif
}
