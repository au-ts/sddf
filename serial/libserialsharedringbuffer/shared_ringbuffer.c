/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "shared_ringbuffer.h"

void ring_init(ring_handle_t *ring, ring_buffer_t *free, ring_buffer_t *used, int buffer_init, uint32_t free_size, uint32_t used_size)
{
    ring->free_ring = free;
    ring->used_ring = used;
    if (buffer_init) {
        ring->free_ring->write_idx = 0;
        ring->free_ring->read_idx = 0;
        ring->free_ring->size = free_size;
        ring->free_ring->notify_writer = false;
        ring->free_ring->notify_reader = false;
        ring->free_ring->plugged = false;
        ring->used_ring->write_idx = 0;
        ring->used_ring->read_idx = 0;
        ring->used_ring->size = used_size;
        ring->used_ring->notify_writer =false;
        ring->used_ring->notify_reader = false;
        ring->used_ring->plugged = false;
    }
}
