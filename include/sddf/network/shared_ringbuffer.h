/*
 * Copyright 2022, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <sddf/network/shared_ringbuffer.h>
#include <sddf/network/constants.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>

typedef struct buff_desc {
    uintptr_t phys_or_offset; /* offset of buffer within buffer memory region or physical address of buffer */
    uint16_t len; /* length of data inside buffer */
} buff_desc_t;

typedef struct ring_buffer {
    uint32_t tail; /* index to insert at */
    uint32_t head; /* index to remove from */
    buff_desc_t buffers[MAX_BUFFS]; /* buffer descripter array - length of array must be equal ro ring buffer size */
    uint32_t size; /* size of the ring buffer */
    bool consumer_signalled; /* flag to indicate whether consumer requires signalling */
} ring_buffer_t;

typedef struct ring_handle {
    ring_buffer_t *free_ring; /* available buffers */
    ring_buffer_t *used_ring; /* filled buffers */
} ring_handle_t;

/**
 * Check if the ring buffer is empty.
 *
 * @param ring ring buffer to check.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline bool ring_empty(ring_buffer_t *ring)
{
    return (ring->tail == ring->head);
}

/**
 * Check if the ring buffer is full.
 *
 * @param ring ring buffer to check.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline bool ring_full(ring_buffer_t *ring)
{
    return (((ring->tail + 1) % ring->size) == ring->head);
}

/**
 * Return the number of buffers in a ring.
 *
 * @param ring ring buffer to check.
 *
 * @return number of buffers in a ring.
 */
static inline uint32_t ring_size(ring_buffer_t *ring)
{
    return (((ring->tail + ring->size) - ring->head) % ring->size);
}

/**
 * Enqueue an element into a ring buffer.
 *
 * @param ring ring buffer to enqueue into.
 * @param buffer buffer descriptor for buffer to be enqueued.
 *
 * @return -1 when ring is full, 0 on success.
 */
static inline int enqueue(ring_buffer_t *ring, buff_desc_t buffer)
{
    if (ring_full(ring)) return -1;

    ring->buffers[ring->tail] = buffer;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    ring->tail = (ring->tail + 1) % ring->size;

    return 0;
}

/**
 * Dequeue an element to a ring buffer.
 *
 * @param ring ring buffer to dequeue from.
 * @param buffer pointer to buffer descriptor for buffer to be dequeued.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue(ring_buffer_t *ring, buff_desc_t *buffer)
{
    if (ring_empty(ring)) return -1;

    *buffer = ring->buffers[ring->head];
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    ring->head = (ring->head + 1) % ring->size;

    return 0;
}

/**
 * Enqueue an element into an free ring buffer.
 *
 * @param ring ring buffer to enqueue into.
 * @param buffer buffer descriptor for buffer to be enqueued.
 *
 * @return -1 when ring is full, 0 on success.
 */
static inline int enqueue_free(ring_handle_t *ring, buff_desc_t buffer)
{
    return enqueue(ring->free_ring, buffer);
}

/**
 * Enqueue an element into a used ring buffer.
 *
 * @param ring ring buffer to enqueue into.
 * @param buffer buffer descriptor for buffer to be enqueued.
 *
 * @return -1 when ring is full, 0 on success.
 */
static inline int enqueue_used(ring_handle_t *ring, buff_desc_t buffer)
{
    return enqueue(ring->used_ring, buffer);
}

/**
 * Dequeue an element from the free ring buffer.
 *
 * @param ring ring handle to dequeue from.
 * @param buffer pointer to buffer descriptor for buffer to be dequeued.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue_free(ring_handle_t *ring, buff_desc_t *buffer)
{
    return dequeue(ring->free_ring, buffer);
}

/**
 * Dequeue an element from a used ring buffer.
 *
 * @param ring ring handle to dequeue from.
 * @param buffer pointer to buffer descriptor for buffer to be dequeued.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue_used(ring_handle_t *ring, buff_desc_t *buffer)
{
    return dequeue(ring->used_ring, buffer);
}

/**
 * Initialise the shared ring buffer.
 *
 * @param ring ring handle to use.
 * @param free pointer to free ring in shared memory.
 * @param used pointer to used ring in shared memory.
 * @param size size of the free and used rings.
 */
void ring_init(ring_handle_t *ring, ring_buffer_t *free, ring_buffer_t *used, uint32_t size);

/**
 * Initialise the free ring by filling with all available ring buffers.
 *
 * @param free_ring ring buffer to fill.
 * @param base_addr start of the memory region the offsets are applied to (only used between mux and driver)
 * @param ring_size size of the ring buffer.
 */
static inline void buffers_init(ring_buffer_t *free_ring, uintptr_t base_addr, uint32_t ring_size)
{
    for (uint32_t i = 0; i < ring_size - 1; i++) {
        buff_desc_t buffer = {(BUFF_SIZE * i) + base_addr, 0};
        int err = enqueue(free_ring, buffer);
        assert(!err);
    }
}

/**
 * Indicate to producer of ring buffer that consumer requires signalling.
 *
 * @param ring_buffer ring buffer that requires signalling upon enqueuing.
 */
static inline void request_signal(ring_buffer_t *ring_buffer)
{
    ring_buffer->consumer_signalled = false;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Indicate to producer of ring buffer that consumer has been signalled.
 *
 * @param ring_buffer ring buffer that has been signalled.
 */
static inline void cancel_signal(ring_buffer_t *ring_buffer)
{
    ring_buffer->consumer_signalled = true;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Consumer requires signalling.
 *
 * @param ring_buffer ring buffer to check.
 */
static inline bool require_signal(ring_buffer_t *ring_buffer)
{
    return !ring_buffer->consumer_signalled;
}