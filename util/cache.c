/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <stdint.h>
#include <sddf/util/cache.h>
#include <sddf/util/util.h>

#ifdef CONFIG_ARCH_AARCH64

/*
 * On ARM, we perform all possible cache operations from user-space. We do not
 * have a cache_invalidate equivalent as the ARM instruction to do so, `dc ivac`,
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

void cache_clean_and_invalidate(unsigned long start, unsigned long end)
{
#if defined(CONFIG_ARCH_AARCH64)
    unsigned long vaddr;
    unsigned long index;

    assert(start != end);

    /* If the end address is not on a cache line boundary, we want to perform
     * the cache operation on that cache line as well. */
    unsigned long end_rounded = ROUND_UP(end, 1 << CONFIG_L1_CACHE_LINE_SIZE_BITS);

    for (index = LINE_INDEX(start); index < LINE_INDEX(end_rounded); index++) {
        vaddr = index << CONFIG_L1_CACHE_LINE_SIZE_BITS;
        asm volatile("dc civac, %0" : : "r"(vaddr));
    }
    asm volatile("dsb sy" ::: "memory");
#elif defined(CONFIG_ARCH_RISCV) || defined(CONFIG_ARCH_X86_64)
    /* While not all RISC-V platforms are DMA cache-cohernet,
     * we assume we are targeting one that is and so there is nothing to do. */
#else
#error "Unknown architecture for cache_clean_and_invalidate"
#endif
}

void cache_clean(unsigned long start, unsigned long end)
{
#if defined(CONFIG_ARCH_AARCH64)
    unsigned long vaddr;
    unsigned long index;

    assert(start != end);

    /* If the end address is not on a cache line boundary, we want to perform
     * the cache operation on that cache line as well. */
    unsigned long end_rounded = ROUND_UP(end, 1 << CONFIG_L1_CACHE_LINE_SIZE_BITS);

    for (index = LINE_INDEX(start); index < LINE_INDEX(end_rounded); index++) {
        vaddr = index << CONFIG_L1_CACHE_LINE_SIZE_BITS;
        asm volatile("dc cvac, %0" : : "r"(vaddr));
    }
    asm volatile("dmb sy" ::: "memory");
#elif defined(CONFIG_ARCH_RISCV) || defined(CONFIG_ARCH_X86_64)
    /* While not all RISC-V platforms are DMA cache-cohernet,
     * we assume we are targeting one that is and so there is nothing to do. */
#else
#error "Unknown architecture for cache_clean"
#endif
}
