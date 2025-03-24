/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/*
 * This is a small utility library for performing cache operations in order
 * to deal with DMA cache coherency. On DMA coherent architectures/platforms
 * (such as certain RISC-V platforms and x86), these operations are no-ops.
 *
 * This library currently has the assumption that all RISC-V platforms are
 * DMA coherent, it does not support platforms with the Zicbom extension.
 */

/*
 * Cleans and invalidates the from start to end. This is not inclusive.
 * If end is on a cache line boundary, the cache line starting at end
 * will not be cleaned/invalidated.
 *
 * On ARM, this operation ultimately performs the 'dc civac' instruction.
 * On RISC-V, this is a no-op.
 */
void cache_clean_and_invalidate(unsigned long start, unsigned long end);

 /*
 * Cleans from start to end. This is not inclusive.
 * If end is on a cache line boundary, the cache line starting at end
 * will not be cleanend.
 *
 * On ARM, this operation ultimately performs the 'dc cvac' instruction.
 * On RISC-V, this is a no-op.
 */
void cache_clean(unsigned long start, unsigned long end);

/*
 * Invalidates from start to end. This is not inclusive.
 *
 * On ARM, this leads to seL4_ARM_VSpace_Invalidate_Data as it is not possible to invalidate
 * directly from user-space. Note that it may be more efficient to simply do a
 * cache_clean_and_invalidate instead as it will not result in a system call.
 * On RISC-V, this is a no-op.
 */
void cache_invalidate(unsigned long start, unsigned long end);
