/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>

typedef struct sddf_queue {
    /* index to insert at */
    uint16_t tail;
    /* index to remove from */
    uint16_t head;
    /* flag to indicate whether consumer requires signalling */
    uint32_t consumer_signalled;
    /* flag to indicate whether producer requires signalling */
    uint32_t producer_signalled;
} sddf_queue_t;

typedef struct sddf_queue_handle {
    sddf_queue_t *queue;
    // TODO: 16 bit enough?
    uint16_t private_tail;
    uint16_t private_head;
    uint32_t capacity;
} sddf_queue_handle_t;

// --------------------------------------------------------
// Reading indices from shared memory
// --------------------------------------------------------

// Trusted API: returns true if there has been an update
// --------------------------------------------------------

static inline bool sddf_queue_cache_head(sddf_queue_handle_t *queue)
{
    uint16_t old_private_head = queue->private_head;
    queue->private_head = load_acquire_32(&queue->queue->head);

    return old_private_head != queue->private_head;
}

static inline bool sddf_queue_cache_tail(sddf_queue_handle_t *queue)
{
    uint16_t old_private_tail = queue->private_tail;
    queue->private_tail = load_acquire_32(&queue->queue->tail);

    return old_private_tail != queue->private_tail;
}

// Untrusted API: Sanity check untrusted index
// --------------------------------------------------------

typedef enum {
    SDDF_QUEUE_ERR_OK = 0,
    SDDF_QUEUE_ERR_HEAD_DECREASE,
    SDDF_QUEUE_ERR_TAIL_DECREASE,
    SDDF_QUEUE_ERR_EXCEED_CAPACITY
} sddf_queue_err_t;

static inline sddf_queue_err_t sddf_queue_check_and_cache_head(sddf_queue_handle_t *queue)
{
    uint16_t old_length = queue->private_tail - queue->private_head;
    queue->private_head = load_acquire_32(&queue->queue->head);

    uint16_t new_length = queue->private_tail - queue->private_head;

    // Clients can only *consume* elements in the queue, thus updates to head
    // are only valid if they *reduce* length
    if (new_length > old_length) {
        return SDDF_QUEUE_ERR_HEAD_DECREASE;
    }

    return SDDF_QUEUE_ERR_OK;
}

static inline bool sddf_queue_check_and_cache_tail(sddf_queue_handle_t *queue)
{
    uint16_t old_length = queue->private_tail - queue->private_head;
    queue->private_tail = load_acquire_32(&queue->queue->tail);

    uint16_t new_length = queue->private_tail - queue->private_head;
    if (new_length < old_length) {
        return SDDF_QUEUE_ERR_TAIL_DECREASE;
    } else if (new_length > queue->capacity) {
        return SDDF_QUEUE_ERR_EXCEED_CAPACITY;
    }

    return SDDF_QUEUE_ERR_OK;
}

// --------------------------------------------------------
// Writing indices to shared memory
// --------------------------------------------------------

static inline bool sddf_queue_flush_head(sddf_queue_handle_t *queue)
{
    store_release_32(&queue->queue->head, queue->private_head);
}

static inline bool sddf_queue_flush_tail(sddf_queue_handle_t *queue)
{
    store_release_32(&queue->queue->head, queue->private_head);
}

// --------------------------------------------------------
// Queue operations - manual cache/flush
// --------------------------------------------------------

static inline uint16_t sddf_queue_cache_length(sddf_queue_handle_t *queue)
{
    return queue->private_tail - queue->private_head;
}

static inline bool sddf_queue_cache_empty(sddf_queue_handle_t *queue)
{
    return sddf_queue_cache_length(queue) == 0;
}

static inline bool sddf_queue_cache_full(sddf_queue_handle_t *queue)
{
    return sddf_queue_cache_length(queue) == queue->capacity;
}

// TODO:
// - Option to automatically flush cache every X enqueues?
static inline bool sddf_queue_cache_enqueue(sddf_queue_handle_t *queue, net_buff_desc_t buffer)
{
    if (sddf_queue_cache_full(queue)) {
        return false;
    }

    queue->queue->buffers[queue->private_tail % queue->capacity] = buffer;
    queue->private_tail++;
    return true;
}

static inline bool sddf_queue_cache_dequeue(sddf_queue_handle_t *queue, net_buff_desc_t *buffer)
{
    if (sddf_queue_cache_empty(queue)) {
        return false;
    }

    *buffer = queue->queue->buffers[queue->private_head % queue->capacity];
    queue->private_head++;
    return true;
}

// --------------------------------------------------------
// Queue operations - auto cache/flush. Assumes trusted neighbour
// --------------------------------------------------------

static inline bool sddf_queue_empty(sddf_queue_handle_t *queue)
{
    // Only re-cache if the queue is empty
    if (!sddf_queue_cache_empty(queue)) {
        return false;
    }

    // Queue is now empty according to private tail, try updating
    return !sddf_queue_cache_tail(queue);
}

static inline bool sddf_queue_full(sddf_queue_handle_t *queue)
{
    // Only re-cache if the queue is full
    if (!sddf_queue_cache_full(queue)) {
        return false;
    }

    // Queue is now full according to private head, try updating
    return !sddf_queue_cache_head(queue);
}

static inline bool sddf_queue_enqueue(sddf_queue_handle_t *queue, net_buff_desc_t buffer)
{
    if (sddf_queue_full(queue)) {
        return false;
    }

    queue->queue->buffers[queue->private_tail % queue->capacity] = buffer;
    queue->private_tail++;
    sddf_queue_flush_tail(queue);

    return true;
}

static inline bool sddf_queue_dequeue(sddf_queue_handle_t *queue, net_buff_desc_t *buffer)
{
    if (sddf_queue_empty(queue)) {
        return false;
    }

    *buffer = queue->queue->buffers[queue->private_head % queue->capacity];
    queue->private_head++;
    sddf_queue_flush_head(queue);

    return true;
}

// TODO: Seems like a waste to have 3 APIs for enqueue/dequeue, but this one is
// necessary if you DON'T want to handle caching your neighbour's index, but you
// DO want to enqueue/dequeue without immediately updating your index
static inline bool sddf_queue_enqueue_private(sddf_queue_handle_t *queue, net_buff_desc_t buffer)
{
    if (sddf_queue_full(queue)) {
        return false;
    }

    queue->queue->buffers[queue->private_tail % queue->capacity] = buffer;
    queue->private_tail++;
    return true;
}

static inline bool sddf_queue_dequeue_private(sddf_queue_handle_t *queue, net_buff_desc_t *buffer)
{
    if (sddf_queue_empty(queue)) {
        return false;
    }

    *buffer = queue->queue->buffers[queue->private_head % queue->capacity];
    queue->private_head++;
    return true;
}

// --------------------------------------------------------
// EXAMPLE: Consumer functions (How to implement caching/reading of tail index)
// --------------------------------------------------------

// Case 1: User updates cache manually, neighbour is trusted
// --------------------------------------------------------

while (!sddf_queue_cache_empty(cons_queue) || sddf_queue_cache_tail(cons_queue))

// Case 2: User updates cache manually, neighbour is untrusted
// --------------------------------------------------------

if (sddf_queue_check_and_cache_tail(cons_queue) != SDDF_QUEUE_ERR_OK) {
    // Cut off client
}

while (!sddf_queue_cache_empty(cons_queue)) {

    // ...

    // Re-cache only when the queue becomes empty
    if (sddf_queue_cache_empty(cons_queue)) {
        if (sddf_queue_check_and_cache_tail(cons_queue) != SDDF_QUEUE_ERR_OK) {
            // Cut off client
        }
    }
}

// Case 3: Library updates cache automatically, neighbour is trusted (this is mandatory with this API)
// --------------------------------------------------------

while (!sddf_queue_empty(cons_queue)) {
    // ...
}

// --------------------------------------------------------
// Remaining functions
// --------------------------------------------------------

static inline void sddf_queue_init(sddf_queue_handle_t *queue_handle, sddf_queue_t *queue, uint16_t init_head, uint16_t init_tail, uint32_t capacity)
{
    queue_handle->queue = queue;
    queue_handle->private_tail = init_tail;
    queue_handle->private_head = init_head;
    queue_handle->capacity = capacity;
}

static inline void sddf_queue_request_producer_signal(sddf_queue_handle_t *queue);
static inline void sddf_queue_cancel_producer_signal(sddf_queue_handle_t *queue);
static inline bool sddf_queue_require_producer_signal(sddf_queue_handle_t *queue);
static inline void sddf_queue_request_consumer_signal(sddf_queue_handle_t *queue);
static inline void sddf_queue_cancel_consumer_signal(sddf_queue_handle_t *queue);
static inline bool sddf_queue_require_rx_queue_cli.free_signal(sddf_queue_handle_t *queue);
