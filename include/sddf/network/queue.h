/*
 * Copyright 2022, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <sddf/network/constants.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>

/**
 * Each function cannot be concurrently called by more than one thread on the same input argument.
 * Different functions can be called concurrently, even though they are accessing the same net_queue_t.
*/

typedef struct net_buff_desc {
    /* offset of buffer within buffer memory region or io address of buffer */
    uint64_t io_or_offset;
    /* length of data inside buffer */
    uint16_t len;
} net_buff_desc_t;

typedef struct net_queue {
    /* index to insert at */
    uint16_t tail;
    /* index to remove from */
    uint16_t head;
    /* flag to indicate whether consumer requires signalling */
    uint32_t consumer_signalled;
    /* buffer descripter array */
    net_buff_desc_t buffers[];
} net_queue_t;

typedef struct net_queue_handle {
    /* available buffers */
    net_queue_t *free;
    /* filled buffers */
    net_queue_t *active;
    /* capacity of the queues */
    uint32_t capacity;
} net_queue_handle_t;

/* Length function used by the consumer of the queue 
(component that modifies the head, but only reads the tail). */
static inline uint16_t net_queue_length_consumer(net_queue_t *queue)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    uint16_t tail = __atomic_load_n(&queue->tail, __ATOMIC_ACQUIRE);
    uint16_t head = __atomic_load_n(&queue->head, __ATOMIC_RELAXED);
    return tail - head;
#else
    COMPILER_MEMORY_ACQUIRE();
    return queue->tail - queue->head;
#endif
}

/* Length function used by the producer of the queue 
(component that modifies the tail, but only reads the head). */
static inline uint16_t net_queue_length_producer(net_queue_t *queue)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    uint16_t tail = __atomic_load_n(&queue->tail, __ATOMIC_RELAXED);
    uint16_t head = __atomic_load_n(&queue->head, __ATOMIC_ACQUIRE);
    return tail - head;
#else
    COMPILER_MEMORY_ACQUIRE();
    return queue->tail - queue->head;
#endif
}

/* Returns the address of the next descriptor entry in
 queue array which points to a valid buffer. Used by the consumer. */
static inline net_buff_desc_t *net_queue_next_full(net_queue_t *queue, uint32_t capacity, uint16_t idx)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    uint16_t head = __atomic_load_n(&queue->head, __ATOMIC_RELAXED);
    uint16_t mod_idx = (head + idx) % capacity;
    return &queue->buffers[mod_idx];
#else
    return &queue->buffers[(queue->head + idx) % capacity];
#endif
}

/* Returns the address of the next descriptor entry in
 queue array which points to an empty slot. Used by the producer. */
static inline net_buff_desc_t *net_queue_next_empty(net_queue_t *queue, uint32_t capacity, uint16_t idx)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    uint16_t tail = __atomic_load_n(&queue->tail, __ATOMIC_RELAXED);
    uint16_t mod_idx = (tail + idx) % capacity;
    return &queue->buffers[mod_idx];
#else
    return &queue->buffers[(queue->tail + idx) % capacity];
#endif
}

/* Used by the consumer to indicate how many buffers have
 been processed. */
static inline void net_queue_publish_dequeued(net_queue_t *queue, uint16_t num_dequeued)
{
    if (!num_dequeued) return;
#if CONFIG_ENABLE_SMP_SUPPORT
    uint16_t head = __atomic_load_n(&queue->head, __ATOMIC_RELAXED);
    __atomic_store_n(&queue->head, head + num_dequeued, __ATOMIC_RELEASE);
#else
    COMPILER_MEMORY_RELEASE();
    queue->head = queue->head + num_dequeued;
#endif
}

/* Used by the producer to indicate how many buffers have
 been inserted. */
static inline void net_queue_publish_enqueued(net_queue_t *queue, uint16_t num_enqueued)
{
    if (!num_enqueued) return;
#if CONFIG_ENABLE_SMP_SUPPORT
    uint16_t tail = __atomic_load_n(&queue->tail, __ATOMIC_RELAXED);
    __atomic_store_n(&queue->tail, tail + num_enqueued, __ATOMIC_RELEASE);
#else
    COMPILER_MEMORY_RELEASE();
    queue->tail = queue->tail + num_enqueued;
#endif
}

/**
 * Initialise the shared queue.
 *
 * @param queue queue handle to use.
 * @param free pointer to free queue in shared memory.
 * @param active pointer to active queue in shared memory.
 * @param capacity capacity of the free and active queues.
 */
static inline void net_queue_init(net_queue_handle_t *queue, net_queue_t *free, net_queue_t *active, uint32_t capacity)
{
    queue->free = free;
    queue->active = active;
    queue->capacity = capacity;
}

/**
 * Initialise the free queue by filling with all free buffers.
 *
 * @param queue queue handle to use.
 * @param base_addr start of the memory region the offsets are applied to (only used between virt and driver)
 */
static inline void net_buffers_init(net_queue_handle_t *queue, uintptr_t base_addr)
{
    for (uint32_t i = 0; i < queue->capacity; i++) {
        net_buff_desc_t *buf = net_queue_next_empty(queue->free, queue->capacity, i);
        buf->io_or_offset = (NET_BUFFER_SIZE * i) + base_addr;
    }
    net_queue_publish_enqueued(queue->free, queue->capacity);
}

/**
 * Indicate to producer of the free queue that consumer requires signalling.
 *
 * @param queue queue handle of free queue that requires signalling upon enqueuing.
 */
static inline void net_request_signal_free(net_queue_handle_t *queue)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    __atomic_store_n(&queue->free->consumer_signalled, 0, __ATOMIC_RELEASE);
#else
    queue->free->consumer_signalled = 0;
#endif
}

/**
 * Indicate to producer of the active queue that consumer requires signalling.
 *
 * @param queue queue handle of active queue that requires signalling upon enqueuing.
 */
static inline void net_request_signal_active(net_queue_handle_t *queue)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    __atomic_store_n(&queue->active->consumer_signalled, 0, __ATOMIC_RELEASE);
#else
    queue->active->consumer_signalled = 0;
#endif
}

/**
 * Indicate to producer of the free queue that consumer has been signalled.
 *
 * @param queue queue handle of the free queue that has been signalled.
 */
static inline void net_cancel_signal_free(net_queue_handle_t *queue)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    __atomic_store_n(&queue->free->consumer_signalled, 1, __ATOMIC_RELEASE);
#else
    queue->free->consumer_signalled = 1;
#endif
}

/**
 * Indicate to producer of the active queue that consumer has been signalled.
 *
 * @param queue queue handle of the active queue that has been signalled.
 */
static inline void net_cancel_signal_active(net_queue_handle_t *queue)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    __atomic_store_n(&queue->active->consumer_signalled, 1, __ATOMIC_RELEASE);
#else
    queue->active->consumer_signalled = 1;
#endif
}

/**
 * Consumer of the free queue requires signalling.
 *
 * @param queue queue handle of the free queue to check.
 */
static inline bool net_require_signal_free(net_queue_handle_t *queue)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    return !__atomic_load_n(&queue->free->consumer_signalled, __ATOMIC_ACQUIRE);
#else
    return !queue->free->consumer_signalled;
#endif
}

/**
 * Consumer of the active queue requires signalling.
 *
 * @param queue queue handle of the active queue to check.
 */
static inline bool net_require_signal_active(net_queue_handle_t *queue)
{
#if CONFIG_ENABLE_SMP_SUPPORT
    return !__atomic_load_n(&queue->active->consumer_signalled, __ATOMIC_ACQUIRE);
#else
    return !queue->active->consumer_signalled;
#endif
}
