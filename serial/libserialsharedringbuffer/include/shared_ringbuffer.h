/*
 * Copyright 2022, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sel4cp.h>
#include "util.h"
#include "fence.h"

#define SIZE 512

/* Buffer descriptor */
typedef struct buff_desc {
    uintptr_t encoded_addr; /* encoded dma addresses */
    unsigned int len; /* associated memory lengths */
    void *cookie; /* index into client side metadata */
} buff_desc_t;

/* Circular buffer containing descriptors */
typedef struct ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size;
    bool notify_writer;
    bool notify_reader;
    bool plugged;
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
void ring_init(ring_handle_t *ring, ring_buffer_t *free, ring_buffer_t *used, int buffer_init, uint32_t free_size, uint32_t used_size);

/**
 * Check if the ring buffer is empty.
 *
 * @param ring ring buffer to check.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline int ring_empty(ring_buffer_t *ring)
{
    return !((ring->write_idx - ring->read_idx) % ring->size);
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
    assert((ring->write_idx - ring->read_idx) >= 0);
    return !((ring->write_idx - ring->read_idx + 1) % ring->size);
}

static inline int ring_size(ring_buffer_t *ring)
{
    assert((ring->write_idx - ring->read_idx) >= 0);
    return (ring->write_idx - ring->read_idx);
}

/**
 * Enqueue an element to a ring buffer
 *
 * @param ring Ring buffer to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 * @param cookie optional pointer to data required on dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int enqueue(ring_buffer_t *ring, uintptr_t buffer, unsigned int len, void *cookie)
{
    assert(buffer != 0);
    if (ring_full(ring)) {
        return -1;
    }

    ring->buffers[ring->write_idx % ring->size].encoded_addr = buffer;
    ring->buffers[ring->write_idx % ring->size].len = len;
    ring->buffers[ring->write_idx % ring->size].cookie = cookie;

    THREAD_MEMORY_RELEASE();
    ring->write_idx++;

    return 0;
}

/**
 * Dequeue an element to a ring buffer.
 *
 * @param ring Ring buffer to Dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 * @param cookie pointer optional pointer to data required on dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue(ring_buffer_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
{
    if (ring_empty(ring)) {
        return -1;
    }

    assert(ring->buffers[ring->read_idx % ring->size].encoded_addr != 0);

    *addr = ring->buffers[ring->read_idx % ring->size].encoded_addr;
    *len = ring->buffers[ring->read_idx % ring->size].len;
    *cookie = ring->buffers[ring->read_idx % ring->size].cookie;

    THREAD_MEMORY_RELEASE();
    ring->read_idx++;

    return 0;
}

/**
 * Enqueue an element into an free ring buffer.
 * This indicates the buffer address parameter is currently free for use.
 *
 * @param ring Ring handle to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 * @param cookie optional pointer to data required on dequeueing.
 *
 * @return -1 when ring is full, 0 on success.
 */
static inline int enqueue_free(ring_handle_t *ring, uintptr_t addr, unsigned int len, void *cookie)
{
    assert(addr);
    return enqueue(ring->free_ring, addr, len, cookie);
}

/**
 * Enqueue an element into a used ring buffer.
 * This indicates the buffer address parameter is currently in use.
 *
 * @param ring Ring handle to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 * @param cookie optional pointer to data required on dequeueing.
 *
 * @return -1 when ring is full, 0 on success.
 */
static inline int enqueue_used(ring_handle_t *ring, uintptr_t addr, unsigned int len, void *cookie)
{
    assert(addr);
    return enqueue(ring->used_ring, addr, len, cookie);
}

/**
 * Dequeue an element from the free ring buffer.
 *
 * @param ring Ring handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 * @param cookie pointer optional pointer to data required on dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue_free(ring_handle_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
{
    return dequeue(ring->free_ring, addr, len, cookie);
}

/**
 * Dequeue an element from a used ring buffer.
 *
 * @param ring Ring handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 * @param cookie pointer optional pointer to data required on dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue_used(ring_handle_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
{
    return dequeue(ring->used_ring, addr, len, cookie);
}

/** 
 * Set the plug of a ring to true.
 * 
 * @param ring Ring handle to plug.
*/
static inline void ring_plug(ring_buffer_t *ring) {
    ring->plugged = true;
}

/** 
 * Set the plug of a ring to false.
 * 
 * @param ring Ring handle to unplug.
*/
static inline void ring_unplug(ring_buffer_t *ring) {
    ring->plugged = false;
}


/**
 * Check the current value of the plug.
 * 
 * @param ring Ring handle to check plug.
 * 
 * @return true when ring is plugged, false when unplugged.
*/
static inline bool ring_plugged(ring_buffer_t *ring) {
    return ring->plugged;
}

/**
 * Dequeue an element from a ring buffer.
 * This function is intended for use by the driver, to collect a pointer
 * into this structure to be passed around as a cookie.
 *
 * @param ring Ring buffer to dequeue from.
 * @param addr pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 * @param cookie pointer to store a pointer to this particular entry.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static int driver_dequeue(ring_buffer_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
{
    if (ring_empty(ring)) {
        return -1;
    }

    *addr = ring->buffers[ring->read_idx % ring->size].encoded_addr;
    *len = ring->buffers[ring->read_idx % ring->size].len;
    *cookie = &ring->buffers[ring->read_idx % ring->size];

    THREAD_MEMORY_RELEASE();
    ring->read_idx++;

    return 0;
}
