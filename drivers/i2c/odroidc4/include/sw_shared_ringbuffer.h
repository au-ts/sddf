/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// sw_shared_ringbuffer.h
// Modified version of Lucy's shared ring buffer code. Stripped down
// for usage as a regular ring buffer as opposed to one targeting DMA.

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sel4cp.h>
#include "fence.h"

#define SIZE 512

/* Buffer descriptor */
typedef struct buff_desc {
    uintptr_t encoded_addr; // Buffer address
    unsigned int len; /* associated memory lengths */
} buff_desc_t;

/* Circular buffer containing descriptors */
typedef struct ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    buff_desc_t buffers[SIZE];
} ring_buffer_t;

/* A ring handle for enqueing/dequeuing into  */
typedef struct ring_handle {
    ring_buffer_t *free_ring;
    ring_buffer_t *used_ring;
} ring_handle_t;

/**
 * Initialise the shared ring buffer.
 *
 * @param ring ring handle to use.
 * @param free pointer to free ring in shared memory.
 * @param used pointer to 'used' ring in shared memory.
 * @param buffer_init 1 indicates the read and write indices in shared memory need to be initialised.
 *                    0 inidicates they do not. Only one side of the shared memory regions needs to do this.
 */
void ring_init(ring_handle_t *ring, ring_buffer_t *free, ring_buffer_t *used, int buffer_init);

/**
 * Check if the ring buffer is empty.
 *
 * @param ring ring buffer to check.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline int ring_empty(ring_buffer_t *ring)
{
    return !((ring->write_idx - ring->read_idx) % SIZE);
}

/**
 * Check if the ring buffer is full
 *
 * @param ring ring buffer to check.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int ring_full(ring_buffer_t *ring)
{
    return !((ring->write_idx - ring->read_idx + 1) % SIZE);
}

static inline int ring_size(ring_buffer_t *ring)
{
    return (ring->write_idx - ring->read_idx);
}


/**
 * Enqueue an element to a ring buffer
 *
 * @param ring Ring buffer to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int enqueue(ring_buffer_t *ring, uintptr_t buffer, unsigned int len)
{
    if (ring_full(ring)) {
        sel4cp_dbg_puts("Ring full");
        return -1;
    }

    ring->buffers[ring->write_idx % SIZE].encoded_addr = buffer;
    ring->buffers[ring->write_idx % SIZE].len = len;
    ring->write_idx++;

    THREAD_MEMORY_RELEASE();

    return 0;
}

/**
 * Dequeue an element to a ring buffer.
 *
 * @param ring Ring buffer to Dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue(ring_buffer_t *ring, uintptr_t *addr, unsigned int *len)
{
    if (ring_empty(ring)) {
        //sel4cp_dbg_puts("Ring is empty");
        return -1;
    }

    *addr = ring->buffers[ring->read_idx % SIZE].encoded_addr;
    *len = ring->buffers[ring->read_idx % SIZE].len;

    THREAD_MEMORY_RELEASE();
    ring->read_idx++;

    return 0;
}

/**
 * Enqueue an element into a free ring buffer.
 * This indicates the buffer address parameter is currently free for re-use.
 *
 * @param ring Ring handle to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int enqueue_free(ring_handle_t *ring, uintptr_t addr, unsigned int len)
{
    return enqueue(ring->free_ring, addr, len);
}

/**
 * Enqueue an element into a used ring buffer.
 * This indicates the buffer address parameter is currently in use.
 *
 * @param ring Ring handle to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int enqueue_used(ring_handle_t *ring, uintptr_t addr, unsigned int len)
{
    return enqueue(ring->used_ring, addr, len);
}

/**
 * Dequeue an element from the free ring buffer.
 *
 * @param ring Ring handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue_free(ring_handle_t *ring, uintptr_t *addr, unsigned int *len)
{
    return dequeue(ring->free_ring, addr, len);
}

/**
 * Dequeue an element from a used ring buffer.
 *
 * @param ring Ring handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue_used(ring_handle_t *ring, uintptr_t *addr, unsigned int *len)
{
    return dequeue(ring->used_ring, addr, len);
}

/**
 * Dequeue an element from a ring buffer.
 * This function is intended for use by the driver, to collect a pointer
 * into this structure to be passed around as a cookie.
 *
 * @param ring Ring buffer to dequeue from.
 * @param addr pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static int driver_dequeue(ring_buffer_t *ring, uintptr_t *addr, unsigned int *len)
{
    if (!((ring->write_idx - ring->read_idx) % SIZE)) {
        return -1;
    }

    *addr = ring->buffers[ring->read_idx % SIZE].encoded_addr;
    *len = ring->buffers[ring->read_idx % SIZE].len;

    THREAD_MEMORY_RELEASE();
    ring->read_idx++;

    return 0;
}
