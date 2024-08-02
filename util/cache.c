#include <microkit.h>
#include <stdint.h>
#include <sddf/util/cache.h>
#include <sddf/util/util.h>

/*
 * This is a small utility library for performing manual cache operations on
 * AArch64 from user-level. The primary use-case is for managing regions of
 * memory that are mapped as cached but are accessible by DMA capable devices.
 */

#ifndef CONFIG_AARCH64_USER_CACHE_ENABLE
#error "CONFIG_AARCH64_USER_CACHE_ENABLE must be enabled"
#error "seL4 must be configured with CONFIG_AARCH64_USER_CACHE_ENABLE"
#endif

#define LINE_INDEX(a) (a >> CONFIG_L1_CACHE_LINE_SIZE_BITS)

static inline void dsb(void)
{
    asm volatile("dsb sy" ::: "memory");
}

static inline void dmb(void)
{
    asm volatile("dmb sy" ::: "memory");
}

static inline void clean_and_invalidate_by_va(unsigned long vaddr)
{
    asm volatile("dc civac, %0" : : "r"(vaddr));
    dsb();
}

static inline void clean_by_va(unsigned long vaddr)
{
    asm volatile("dc cvac, %0" : : "r"(vaddr));
    dmb();
}

// Intentionally no invalidate_by_va or cache_invalidate. The ARM instruction
// for that -- `dc ivac` -- does not work in userspace (EL0). See [1].
//
// [1]: https://developer.arm.com/documentation/ddi0595/2021-06/AArch64-Instructions/DC-IVAC--Data-or-unified-Cache-line-Invalidate-by-VA-to-PoC

/*
 * Cleans and invalidates the from start to end. This is not inclusive.
 * If end is on a cache line boundary, the cache line starting at end
 * will not be cleaned/invalidated.
 *
 * This operation ultimately performs the 'dc civac' instruction.
 */
void cache_clean_and_invalidate(unsigned long start, unsigned long end)
{
    unsigned long vaddr;
    unsigned long index;

    assert(start != end);

    /* If the end address is not on a cache line boundary, we want to perform
     * the cache operation on that cache line as well. */
    unsigned long end_rounded = ROUND_UP(end, CONFIG_L1_CACHE_LINE_SIZE_BITS);

    for (index = LINE_INDEX(start); index < LINE_INDEX(end_rounded); index++) {
        vaddr = index << CONFIG_L1_CACHE_LINE_SIZE_BITS;
        clean_and_invalidate_by_va(vaddr);
    }
}

/*
 * Cleans from start to end. This is not inclusive.
 * If end is on a cache line boundary, the cache line starting at end
 * will not be cleanend.
 *
 * This operation ultimately performs the 'dc civac' instruction.
 */
void cache_clean(unsigned long start, unsigned long end)
{
    unsigned long vaddr;
    unsigned long index;

    assert(start != end);

    /* If the end address is not on a cache line boundary, we want to perform
     * the cache operation on that cache line as well. */
    unsigned long end_rounded = ROUND_UP(end, CONFIG_L1_CACHE_LINE_SIZE_BITS);

    for (index = LINE_INDEX(start); index < LINE_INDEX(end_rounded); index++) {
        vaddr = index << CONFIG_L1_CACHE_LINE_SIZE_BITS;
        clean_by_va(vaddr);
    }
}
