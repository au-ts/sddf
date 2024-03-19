/*
 * Copyright 2022, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <sddf/network/queue.h>
#include <sddf/network/constants.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>

typedef struct net_buff_desc {
    /* offset of buffer within buffer memory region or physical address of buffer */
    uintptr_t phys_or_offset;
    /* length of data inside buffer */
    uint16_t len;
} net_buff_desc_t;

typedef struct net_queue {
    /* index to insert at */
    uint32_t tail;
    /* index to remove from */
    uint32_t head;
    /* buffer descripter array - length of array must be equal to queue size */
    net_buff_desc_t buffers[NET_MAX_BUFFERS];
    /* size of the queue */
    uint32_t size;
    /* flag to indicate whether consumer requires signalling */
    bool consumer_signalled;
} net_queue_t;

typedef struct net_queue_handle {
     /* available buffers */
    net_queue_t *free;
     /* filled buffers */
    net_queue_t *active;
} net_queue_handle_t;

/**
 * Check if the queue is empty.
 *
 * @param queue queue to check.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline bool net_queue_empty(net_queue_t *queue)
{
    return (queue->tail == queue->head);
}

/**
 * Check if the queue is full.
 *
 * @param queue queue to check.
 *
 * @return true indicates the queue is full, false otherwise.
 */
static inline bool net_queue_full(net_queue_t * queue)
{
    return (((queue->tail + 1) % queue->size) == queue->head);
}

/**
 * Return the number of buffers in a queue.
 *
 * @param queue queue to check.
 *
 * @return number of buffers in a queue.
 */
static inline uint32_t net_queue_size(net_queue_t * queue)
{
    return (((queue->tail + queue->size) - queue->head) % queue->size);
}

/**
 * Enqueue an element into a queue.
 *
 * @param queue queue to enqueue into.
 * @param buffer buffer descriptor for buffer to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int net_enqueue(net_queue_t *queue, net_buff_desc_t buffer)
{
    if (net_queue_full(queue)) return -1;

    queue->buffers[queue->tail] = buffer;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    queue->tail = (queue->tail + 1) % queue->size;

    return 0;
}

/**
 * Dequeue an element to a queue.
 *
 * @param queue queue to dequeue from.
 * @param buffer pointer to buffer descriptor for buffer to be dequeued.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int net_dequeue(net_queue_t *queue, net_buff_desc_t *buffer)
{
    if (net_queue_empty(queue)) return -1;

    *buffer = queue->buffers[queue->head];
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
    queue->head = (queue->head + 1) % queue->size;

    return 0;
}

/**
 * Enqueue an element into an free queue.
 *
 * @param queue queue to enqueue into.
 * @param buffer buffer descriptor for buffer to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int net_enqueue_free(net_queue_handle_t *queue, net_buff_desc_t buffer)
{
    return net_enqueue(queue->free, buffer);
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
    return net_enqueue(queue->active, buffer);
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
    return net_dequeue(queue->free, buffer);
}

/**
 * Dequeue an element from an active queue.
 *
 * @param queue queue handle to dequeue from.
 * @param buffer pointer to buffer descriptor for buffer to be dequeued.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int net_dequeue_active(net_queue_handle_t *queue, net_buff_desc_t *buffer)
{
    return net_dequeue(queue->active, buffer);
}

/**
 * Initialise the shared queue.
 *
 * @param queue queue handle to use.
 * @param free pointer to free queue in shared memory.
 * @param active pointer to active queue in shared memory.
 * @param size size of the free and active queues.
 */
static inline void net_queue_init(net_queue_handle_t *queue, net_queue_t *free, net_queue_t *active, uint32_t size)
{
    queue->free = free;
    queue->active = active;
    queue->free->size = size;
    queue->active->size = size;
}

/**
 * Initialise the free queue by filling with all free buffers.
 *
 * @param free queue to fill.
 * @param base_addr start of the memory region the offsets are applied to (only used between virt and driver)
 * @param queue_size size of the queue.
 */
static inline void net_buffers_init(net_queue_t *free, uintptr_t base_addr, uint32_t queue_size)
{
    for (uint32_t i = 0; i < queue_size - 1; i++) {
        net_buff_desc_t buffer = {(ETH_BUFFER_SIZE * i) + base_addr, 0};
        int err = net_enqueue(free, buffer);
        assert(!err);
    }
}

/**
 * Indicate to producer of queue that consumer requires signalling.
 *
 * @param queue queue that requires signalling upon enqueuing.
 */
static inline void net_request_signal(net_queue_t *queue)
{
    queue->consumer_signalled = false;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Indicate to producer of queue that consumer has been signalled.
 *
 * @param queue queue that has been signalled.
 */
static inline void net_cancel_signal(net_queue_t *queue)
{
    queue->consumer_signalled = true;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Consumer requires signalling.
 *
 * @param queue queue to check.
 */
static inline bool net_require_signal(net_queue_t *queue)
{
    return !queue->consumer_signalled;
}
