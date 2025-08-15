/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/util/printf.h>

#include <dma_client.h>

__attribute__((__section__(".shared_memory"))) void *shared_memory = {};

void init()
{
    auto memory = (uint64_t *)shared_memory;

    for (int i = 0; i < 16; i++) {
        memory[i] = i;
    }

    dma_copy(16 * sizeof(uint64_t), 0 * sizeof(uint64_t), 16 * sizeof(uint64_t));

    for (int i = 16; i < 32; i++) {
        sddf_dprintf("%zu ", memory[i]);
    }
    sddf_dprintf("\nsuccess\n");
}

void notified([[maybe_unused]] microkit_channel ch)
{
}
