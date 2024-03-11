/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/network/shared_ringbuffer.h>

void ring_init(ring_handle_t *ring, ring_buffer_t *free, ring_buffer_t *used, uint32_t size)
{
    ring->free_ring = free;
    ring->used_ring = used;
    ring->free_ring->size = size;
    ring->used_ring->size = size;
}