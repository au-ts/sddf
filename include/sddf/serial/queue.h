/*
 * Copyright 2022, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>

/**
 * The serial queue, like all sDDF queues, is an implementation of a single-producer,
 * single-consumer FIFO queue. The key assumption being that only the producer is permitted to
 * modify the tail, and only the consumer is permitted to modify the head. Both components are
 * permitted to read both indices. The library's atomic operations are written to ensure correctness
 * under these assumptions, thus each function's description contains an explicit notes on its
 * assumed caller.
 */

typedef struct serial_queue {
    /* index to insert at */
    uint32_t tail;
    /* index to remove from */
    uint32_t head;
    /* flag to indicate whether producer requires signalling */
    uint32_t producer_signalled;
} serial_queue_t;

typedef struct serial_queue_handle {
    serial_queue_t *queue;
    uint32_t capacity;
    char *data_region;
} serial_queue_handle_t;

/**
 * Return the number of bytes of data stored in the queue. This is calculated by
 * using the head and tail values currently stored in the shared queue handle
 * data structure. This function should only be called by the CONSUMER of the
 * queue.
 *
 * @param queue_handle queue containing the data.
 *
 * @return The number bytes of data stored in the queue.
 */
static inline uint32_t serial_queue_length_consumer(serial_queue_handle_t *queue_handle)
{
    /* The load-acquire will be paired with the store-release
     * in serial_enqueue() or serial_update_shared_tail().
     */
    uint32_t tail = load_acquire_32(&queue_handle->queue->tail);
    uint32_t head = queue_handle->queue->head;
    return tail - head;
}

/**
 * Return the number of bytes of data stored in the queue. This is calculated by
 * using the head and tail values currently stored in the shared queue handle
 * data structure. This function should only be called by the PRODUCER of the
 * queue.
 *
 * @param queue_handle queue containing the data.
 *
 * @return The number bytes of data stored in the queue.
 */
static inline uint32_t serial_queue_length_producer(serial_queue_handle_t *queue_handle)
{
    uint32_t tail = queue_handle->queue->tail;
    /* The load-acquire will be paired with the store-release
     * in serial_dequeue() or serial_update_shared_head().
     */
    uint32_t head = load_acquire_32(&queue_handle->queue->head);
    return tail - head;
}

/**
 * Check if the queue is empty. This function should only be called by the
 * CONSUMER of the queue.
 *
 * @param queue_handle queue to check.
 * @param local_head head which points to the next character to be dequeued.
 * Should be set to the value of the shared head in the queue if a local copy is
 * not in use.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline int serial_queue_empty(serial_queue_handle_t *queue_handle, uint32_t local_head)
{
    /* The load-acquire will be paired with the store-release
     * in serial_enqueue() or serial_update_shared_tail().
     */
    uint32_t tail = load_acquire_32(&queue_handle->queue->tail);

    return local_head == tail;
}

/**
 * Check if the queue is full. This function should only be called by the
 * PRODUCER of the queue.
 *
 * @param queue_handle queue to check.
 * @param local_tail tail which points to the next enqueue slot. Should be set
 * to the value of the shared tail in the queue if a local copy is not in use.
 *
 * @return true indicates the queue is full, false otherwise.
 */
static inline int serial_queue_full(serial_queue_handle_t *queue_handle, uint32_t local_tail)
{
    /* The load-acquire will be paired with the store-release
     * in serial_dequeue() or serial_update_shared_head().
     */
    uint32_t head = load_acquire_32(&queue_handle->queue->head);

    return local_tail - head == queue_handle->capacity;
}

/**
 * Enqueue a character into a queue. Update the shared tail so the character is
 * visible to the consumer. This function should only be called by the PRODUCER
 * of the queue.
 *
 * @param queue_handle queue to enqueue into.
 * @param character character to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int serial_enqueue(serial_queue_handle_t *queue_handle, char character)
{
    uint32_t *tail = &queue_handle->queue->tail;

    if (serial_queue_full(queue_handle, *tail)) {
        return -1;
    }

    queue_handle->data_region[*tail % queue_handle->capacity] = character;

    /* The store-release will synchronise with load-acquires by the CONSUMER of the queue. */
    store_release_32(tail, *tail + 1);

    return 0;
}

/**
 * Enqueue a character locally into a queue. Update a local tail variable so the
 * character is not visible to the consumer. This function should only be called
 * by the PRODUCER of the queue.
 *
 * @param queue_handle queue to enqueue into.
 * @param local_tail address of the tail to be used and incremented.
 * @param character character to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int serial_enqueue_local(serial_queue_handle_t *queue_handle, uint32_t *local_tail, char character)
{
    if (serial_queue_full(queue_handle, *local_tail)) {
        return -1;
    }

    queue_handle->data_region[*local_tail % queue_handle->capacity] = character;
    (*local_tail)++;

    return 0;
}

/**
 * Dequeue a character from a queue. Update the shared head so the removal of
 * the character is visible to the producer. This function should only be called
 * by the CONSUMER of the queue.
 *
 * @param queue_handle queue to dequeue from.
 * @param character address of character to copy into.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int serial_dequeue(serial_queue_handle_t *queue_handle, char *character)
{
    uint32_t *head = &queue_handle->queue->head;

    if (serial_queue_empty(queue_handle, *head)) {
        return -1;
    }

    *character = queue_handle->data_region[*head % queue_handle->capacity];

    /* The store-release will synchronise with load-acquires by the PRODUCER of the queue. */
    store_release_32(head, *head + 1);

    return 0;
}

/**
 * Dequeue a character locally from a queue. Update a local head variable so the
 * removal of the character is not visible to the producer. This function should
 * only be called by the CONSUMER of the queue.
 *
 * @param queue_handle queue to dequeue from.
 * @param local_head address of the head to be used and incremented.
 * @param character character to copy into.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int serial_dequeue_local(serial_queue_handle_t *queue_handle, uint32_t *local_head, char *character)
{
    if (serial_queue_empty(queue_handle, *local_head)) {
        return -1;
    }

    *character = queue_handle->data_region[*local_head % queue_handle->capacity];
    (*local_head)++;

    return 0;
}

/**
 * Update the value of the tail in the shared data structure to make locally
 * enqueued data visible. This function should only be called by the PRODUCER of
 * the queue.
 *
 * @param queue_handle queue to update.
 * @param local_tail tail which points to the last character enqueued.
 */
static inline void serial_update_shared_tail(serial_queue_handle_t *queue_handle, uint32_t local_tail)
{
#ifdef CONFIG_DEBUG_BUILD
    /* The load-acquire will be paired with the store-release
     * in serial_dequeue() or serial_update_shared_head().
     */
    uint32_t head = load_acquire_32(&queue_handle->queue->head);
    uint32_t current_tail = queue_handle->queue->tail;

    uint32_t current_length = current_tail - head;
    uint32_t new_length = local_tail - head;

    /* Ensure updates to tail do not decrease data length */
    assert(new_length >= current_length);

    /* Ensure updates to tail don't exceed capacity restraints */
    assert(new_length <= queue_handle->capacity);
#endif

    /* The store-release will synchronise with load-acquires by the CONSUMER of the queue. */
    store_release_32(&queue_handle->queue->tail, local_tail);
}

/**
 * Update the value of the head in the shared data structure to make local
 * dequeues visible. This function should only be called by the CONSUMER of the
 * queue.
 *
 * @param queue_handle queue to update.
 * @param local_head head which points to the next character to dequeue.
 */
static inline void serial_update_shared_head(serial_queue_handle_t *queue_handle, uint32_t local_head)
{
#ifdef CONFIG_DEBUG_BUILD
    /* The load-acquire will be paired with the store-release
     * in serial_enqueue() or serial_update_shared_tail().
     */
    uint32_t tail = load_acquire_32(&queue_handle->queue->tail);
    uint32_t current_head = queue_handle->queue->head;

    uint32_t current_length = tail - current_head;
    uint32_t new_length = tail - local_head;

    /* Ensure updates to head don't increase data length or violate capacity
    constraints */
    assert(new_length <= current_length);
#endif

    /* The store-release will synchronise with load-acquires by the PRODUCER of the queue. */
    store_release_32(&queue_handle->queue->head, local_head);
}

/**
 * Return the number of bytes of data stored contiguously in the queue from the
 * head index to either the tail index or the end of the data region. This
 * function should only be called by the CONSUMER of the queue.
 *
 * @param queue_handle queue containing the data.
 *
 * @return Number of bytes stored contiguously in the queue.
 */
static inline uint32_t serial_queue_contiguous_length(serial_queue_handle_t *queue_handle)
{
    uint32_t head = queue_handle->queue->head;
    uint32_t length = serial_queue_length_consumer(queue_handle);

    return MIN(queue_handle->capacity - (head % queue_handle->capacity), length);
}

/**
 * Return the number of free bytes remaining in the queue. This is the number of
 * bytes that can be enqueued until the queue is full. This function should only
 * be called by the PRODUCER of the queue.
 *
 * @param queue_handle queue to be filled with data.
 *
 * @return The amount of free space remaining in the queue.
 */
static inline uint32_t serial_queue_free(serial_queue_handle_t *queue_handle)
{
    uint32_t length = serial_queue_length_producer(queue_handle);

    return queue_handle->capacity - length;
}

/**
 * Return the number of bytes that can be copied into the queue contiguously.
 * This is the number of bytes that can be copied into the queue with a single
 * call of memcpy. This function should only be called by the PRODUCER of the
 * queue.
 *
 * @param queue_handle queue to be filled with data.
 *
 * @return The amount of contiguous free space remaining in the queue.
 */
static inline uint32_t serial_queue_contiguous_free(serial_queue_handle_t *queue_handle)
{
    return MIN(queue_handle->capacity - (queue_handle->queue->tail % queue_handle->capacity),
               serial_queue_free(queue_handle));
}

/**
 * Enqueue a buffer of contiguous characters into a queue. This function should
 * only be called by the PRODUCER of the queue.
 *
 * @param queue_handle queue to be filled with data.
 * @param num number of characters to enqueue.
 * @param src pointer to characters to be transferred.
 *
 * @return Number of characters actually enqueued.
 */
static inline uint32_t serial_enqueue_batch(serial_queue_handle_t *queue_handle, uint32_t num, const char *src)
{
    char *dst = queue_handle->data_region + (queue_handle->queue->tail % queue_handle->capacity);
    uint32_t avail = serial_queue_free(queue_handle);
    uint32_t num_prewrap;
    uint32_t num_postwrap;

    num = MIN(num, avail);
    num_prewrap = serial_queue_contiguous_free(queue_handle);
    num_prewrap = MIN(num, num_prewrap);
    num_postwrap = num - num_prewrap;

    memcpy(dst, src, num_prewrap);
    if (num_postwrap) {
        memcpy(queue_handle->data_region, src + num_prewrap, num_postwrap);
    }

    serial_update_shared_tail(queue_handle, queue_handle->queue->tail + num);

    return num;
}

/**
 * Transfer all data from a consumer queue to a producer queue. Assumes there is
 * enough free space in the free queue to fit all data in the active queue. This
 * function should only be called by the CONSUMER of the active queue, and the
 * PRODUCER of the free queue.
 *
 * @param free_queue_handle queue to produce into.
 * @param active_queue_handle queue to consume.
 */
static inline void serial_transfer_all(serial_queue_handle_t *free_queue_handle,
                                       serial_queue_handle_t *active_queue_handle)
{
    /* The caller is the consumer of the active queue */
    uint32_t active_capacity = active_queue_handle->capacity;
    uint32_t active_head = active_queue_handle->queue->head;
    uint32_t active_length = load_acquire_32(&active_queue_handle->queue->tail) - active_head;

#ifdef CONFIG_DEBUG_BUILD
    /* The caller is the producer of the free queue.
     * The load-acquire will be paired with the store-release
     * in serial_dequeue() or serial_update_shared_head()
     */
    uint32_t free_length = serial_queue_free(free_queue_handle);

    assert(active_length <= free_length);
#endif

    /* Copy in contiguous chunks */
    while (active_length) {
        uint32_t active_batch = MIN(active_capacity - (active_head % active_capacity), active_length);
        char *src = active_queue_handle->data_region + (active_head % active_capacity);

        uint32_t transferred = serial_enqueue_batch(free_queue_handle, active_batch, src);
        assert(transferred == active_batch);

        active_head += active_batch;
        serial_update_shared_head(active_queue_handle, active_head);
        /* The load-acquire will be paired with the store-release
         * in serial_enqueue() or serial_update_shared_tail().
         */
        active_length = load_acquire_32(&active_queue_handle->queue->tail) - active_head;
    }
}

/**
 * Transfer all data from a consumer queue to a producer queue, adding colour codes
 * before and after. Assumes there is enough free space in the free queue to fit
 * all data in the active. This function should only be called by the CONSUMER
 * of the active queue, and the PRODUCER of the free queue.
 *
 * @param free_queue_handle queue to produce into.
 * @param active_queue_handle queue to consume.
 * @param col_start colour code start string.
 * @param col_start_len length of start string.
 * @param col_end colour code end string.
 * @param col_end_len length of end string.
 */
static inline void serial_transfer_all_colour(serial_queue_handle_t *free_queue_handle,
                                              serial_queue_handle_t *active_queue_handle, const char *col_start,
                                              uint16_t col_start_len, const char *col_end, uint16_t col_end_len)
{
#ifdef CONFIG_DEBUG_BUILD
    /* The caller is the consumer of the active queue */
    uint32_t active_length = serial_queue_length_consumer(active_queue_handle);

    /* The caller is the producer of the free queue */
    uint32_t free_length = serial_queue_free(free_queue_handle);

    assert(active_length + col_start_len + col_end_len <= free_length);
#endif

    /* Transfer col_start string */
    uint32_t transferred = serial_enqueue_batch(free_queue_handle, col_start_len, col_start);
    assert(transferred == col_start_len);

    /* Transfer active data */
    serial_transfer_all(free_queue_handle, active_queue_handle);

    /* Transfer col_end string */
    transferred = serial_enqueue_batch(free_queue_handle, col_end_len, col_end);
    assert(transferred == col_end_len);
}

/**
 * Initialise the queue handle data structure with the shared queue.
 *
 * @param queue_handle queue handle to use.
 * @param queue pointer to queue in shared memory.
 * @param capacity capacity of the queue.
 * @param data_region address of the data region.
 */
static inline void serial_queue_init(serial_queue_handle_t *queue_handle, serial_queue_t *queue, uint32_t capacity,
                                     char *data_region)
{
    queue_handle->queue = queue;
    queue_handle->capacity = capacity;
    queue_handle->data_region = data_region;
}

/**
 * Indicate to consumer of the queue that producer requires signalling.
 *
 * @param queue queue handle of queue that requires signalling upon enqueuing.
 */
static inline void serial_request_consumer_signal(serial_queue_handle_t *queue_handle)
{
    queue_handle->queue->producer_signalled = 0;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Indicate that producer has been signalled.
 *
 * @param queue queue handle of the queue that has been signalled.
 */
static inline void serial_cancel_consumer_signal(serial_queue_handle_t *queue_handle)
{
    queue_handle->queue->producer_signalled = 1;
#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif
}

/**
 * Producer of the queue requires signalling.
 *
 * @param queue queue handle of the queue to check.
 */
static inline bool serial_require_consumer_signal(serial_queue_handle_t *queue_handle)
{
    return !queue_handle->queue->producer_signalled;
}
