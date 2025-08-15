/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <sddf/util/printf.h>

static void dma_copy(uint64_t dest_offset, uint64_t src_offset, uint64_t count)
{
#ifdef CONFIG_DEBUG_BUILD
    if (dest_offset < src_offset + count) {
        sddf_dprintf("invalid dma_copy param: %zu %zu %zu\n", dest_offset, src_offset, count);
        microkit_internal_crash(0);
    }
#endif
    sddf_set_mr(0, dest_offset);
    sddf_set_mr(1, src_offset);
    sddf_set_mr(2, count);
    sddf_ppcall(0, microkit_msginfo_new(0, 3));
}
