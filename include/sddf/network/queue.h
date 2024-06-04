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

// Pancake Todo: Change `uint64_t len` etc back to same int type as C sDDF network queue
// when pancake supports non-shared memory load/store for 16 and 32 bits

typedef struct net_buff_desc {
    /* offset of buffer within buffer memory region or io address of buffer */
    uint64_t io_or_offset;
    /* length of data inside buffer */
    uint64_t len;
} net_buff_desc_t;

typedef struct net_queue {
    /* index to insert at */
    uint64_t tail;
    /* index to remove from */
    uint64_t head;
    /* flag to indicate whether consumer requires signalling */
    uint64_t consumer_signalled;
    /* buffer descripter array */
    net_buff_desc_t buffers[];
} net_queue_t;

typedef struct net_queue_handle {
    /* available buffers */
    net_queue_t *free;
    /* filled buffers */
    net_queue_t *active;
    /* capacity of the queues */
    uint64_t capacity;
} net_queue_handle_t;

////////////// To stay consistent with Pancake implementation
static inline bool net_queue_empty(net_queue_t *queue)
{
    return queue->tail == queue->head;
}

static inline bool net_queue_full(net_queue_t *queue, uint64_t capacity)
{
    uint64_t new_tail = (queue->tail + 1) % capacity;
    return (new_tail == queue->head);
}

static inline void net_enqueue(net_queue_t *queue, net_buff_desc_t buffer, uint64_t capacity)
{
    queue->buffers[queue->tail] = buffer;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    queue->tail = (queue->tail + 1) % capacity;
}

static inline net_buff_desc_t* net_dequeue(net_queue_t *queue, uint64_t capacity)
{
    net_buff_desc_t* buffer = &queue->buffers[queue->head];
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    queue->head = (queue->head + 1) % capacity;
    return buffer;
}

static inline void net_request_signal(net_queue_t *queue)
{
    queue->consumer_signalled = 0;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

static inline void net_cancel_signal(net_queue_t *queue)
{
    queue->consumer_signalled = 1;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

static inline bool net_require_signal(net_queue_t *queue)
{
    return !queue->consumer_signalled;
}

//////////////
/**
 * Get the number of buffers enqueued into a queue.
 *
 * @param queue queue handle for the queue to get the length of.
 *
 * @return number of buffers enqueued into a queue.
 */
static inline uint16_t net_queue_length(net_queue_t *queue)
{
    return queue->tail - queue->head;
}

/**
 * Check if the free queue is empty.
 *
 * @param queue queue handle for the free queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline bool net_queue_empty_free(net_queue_handle_t *queue)
{
    return queue->free->tail - queue->free->head == 0;
}

/**
 * Check if the active queue is empty.
 *
 * @param queue queue handle for the active queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline bool net_queue_empty_active(net_queue_handle_t *queue)
{
    return queue->active->tail - queue->active->head == 0;
}

/**
 * Check if the free queue is full.
 *
 * @param queue queue handle for the free queue to check.
 *
 * @return true indicates the queue is full, false otherwise.
 */
static inline bool net_queue_full_free(net_queue_handle_t *queue)
{
    return (queue->free->tail + 1) % queue->capacity == queue->free->head;
}

/**
 * Check if the active queue is full.
 *
 * @param queue queue handle for the active queue to check.
 *
 * @return true indicates the queue is full, false otherwise.
 */
static inline bool net_queue_full_active(net_queue_handle_t *queue)
{
    return (queue->active->tail + 1) % queue->capacity == queue->active->head;
}

/**
 * Enqueue an element into a free queue.
 *
 * @param queue queue to enqueue into.
 * @param buffer buffer descriptor for buffer to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int net_enqueue_free(net_queue_handle_t *queue, net_buff_desc_t buffer)
{
    if (net_queue_full_free(queue)) {
        return -1;
    }

    queue->free->buffers[queue->free->tail % queue->capacity] = buffer;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    queue->free->tail = (queue->free->tail + 1) % queue->capacity;

    return 0;
}

/**
 * Enqueue an element into an active queue.
 *
 * @param queue queue to enqueue into.
 * @param buffer buffer descriptor for buffer to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int net_enqueue_active(net_queue_handle_t *queue, net_buff_desc_t buffer)
{
    if (net_queue_full_active(queue)) {
        return -1;
    }

    queue->active->buffers[queue->active->tail % queue->capacity] = buffer;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    queue->active->tail = (queue->active->tail + 1) % queue->capacity;

    return 0;
}

/**
 * Dequeue an element from the free queue.
 *
 * @param queue queue handle to dequeue from.
 * @param buffer pointer to buffer descriptor for buffer to be dequeued.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int net_dequeue_free(net_queue_handle_t *queue, net_buff_desc_t *buffer)
{
    if (net_queue_empty_free(queue)) {
        return -1;
    }

    *buffer = queue->free->buffers[queue->free->head % queue->capacity];
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    queue->free->head = (queue->free->head + 1) % queue->capacity;

    return 0;
}

/**
 * Dequeue an element from the active queue.
 *
 * @param queue queue handle to dequeue from.
 * @param buffer pointer to buffer descriptor for buffer to be dequeued.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int net_dequeue_active(net_queue_handle_t *queue, net_buff_desc_t *buffer)
{
    if (net_queue_empty_active(queue)) {
        return -1;
    }

    *buffer = queue->active->buffers[queue->active->head % queue->capacity];
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    queue->active->head = (queue->active->head + 1) % queue->capacity;

    return 0;
}

/**
 * Initialise the shared queue.
 *
 * @param queue queue handle to use.
 * @param free pointer to free queue in shared memory.
 * @param active pointer to active queue in shared memory.
 * @param capacity capacity of the free and active queues.
 */
static inline void net_queue_init(net_queue_handle_t *queue, net_queue_t *free, net_queue_t *active, uint64_t capacity)
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
    for (uint64_t i = 0; i < queue->capacity - 1; i++) {
        net_buff_desc_t buffer = {(NET_BUFFER_SIZE * i) + base_addr, 0};
        int err = net_enqueue_free(queue, buffer);
        assert(!err);
    }
}

/**
 * Indicate to producer of the free queue that consumer requires signalling.
 *
 * @param queue queue handle of free queue that requires signalling upon enqueuing.
 */
static inline void net_request_signal_free(net_queue_handle_t *queue)
{
    queue->free->consumer_signalled = 0;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Indicate to producer of the active queue that consumer requires signalling.
 *
 * @param queue queue handle of active queue that requires signalling upon enqueuing.
 */
static inline void net_request_signal_active(net_queue_handle_t *queue)
{
    queue->active->consumer_signalled = 0;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Indicate to producer of the free queue that consumer has been signalled.
 *
 * @param queue queue handle of the free queue that has been signalled.
 */
static inline void net_cancel_signal_free(net_queue_handle_t *queue)
{
    queue->free->consumer_signalled = 1;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Indicate to producer of the active queue that consumer has been signalled.
 *
 * @param queue queue handle of the active queue that has been signalled.
 */
static inline void net_cancel_signal_active(net_queue_handle_t *queue)
{
    queue->active->consumer_signalled = 1;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Consumer of the free queue requires signalling.
 *
 * @param queue queue handle of the free queue to check.
 */
static inline bool net_require_signal_free(net_queue_handle_t *queue)
{
    return !queue->free->consumer_signalled;
}

/**
 * Consumer of the active queue requires signalling.
 *
 * @param queue queue handle of the active queue to check.
 */
static inline bool net_require_signal_active(net_queue_handle_t *queue)
{
    return !queue->active->consumer_signalled;
}
