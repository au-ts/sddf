/*
 * Copyright 2022, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>

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
 * Return the number of bytes of data stored in the queue.
 *
 * @param queue_handle queue containing the data.
 *
 * @return The number bytes of data stored in the queue.
 */
static inline uint32_t serial_queue_length(serial_queue_handle_t *queue_handle)
{
    return queue_handle->queue->tail - queue_handle->queue->head;
}

/**
 * Check if the queue is empty.
 *
 * @param queue_handle queue to check.
 * @param local_head head which points to the next character to be dequeued.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline int serial_queue_empty(serial_queue_handle_t *queue_handle, uint32_t local_head)
{
    return local_head == queue_handle->queue->tail;
}

/**
 * Check if the queue is full.
 *
 * @param queue_handle queue to check.
 * @param local_tail tail which points to the next enqueue slot.
 *
 * @return true indicates the queue is full, false otherwise.
 */
static inline int serial_queue_full(serial_queue_handle_t *queue_handle, uint32_t local_tail)
{
    return local_tail - queue_handle->queue->head == queue_handle->capacity;
}

/**
 * Enqueue a character into a queue. Update the shared tail so the character
 * is visible to the consumer.
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
    (*tail)++;

    return 0;
}

/**
 * Enqueue a character locally into a queue. Update a local tail variable so the
 * character is not visible to the consumer.
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
 * Dequeue a character from a queue. Update the shared head so the removal of the
 * character is visible to the producer.
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
    (*head)++;

    return 0;
}

/**
 * Dequeue a character locally from a queue. Update a local head variable so the
 * removal of the character is not visible to the producer.
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
 * Update the value of the tail in the shared data structure to make
 * locally enqueued data visible.
 *
 * @param queue_handle queue to update.
 * @param local_tail tail which points to the last character enqueued.
 */
static inline void serial_update_shared_tail(serial_queue_handle_t *queue_handle, uint32_t local_tail)
{
    uint32_t current_length = serial_queue_length(queue_handle);
    uint32_t new_length = local_tail - queue_handle->queue->head;

    /* Ensure updates to tail don't overwrite existing data */
    assert(new_length >= current_length);

    /* Ensure updates to tail don't exceed capacity restraints */
    assert(new_length <= queue_handle->capacity);

#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif

    queue_handle->queue->tail = local_tail;
}

/**
 * Update the value of the head in the shared data structure to make
 * local dequeues visible.
 *
 * @param queue_handle queue to update.
 * @param local_head head which points to the next character to dequeue.
 */
static inline void serial_update_shared_head(serial_queue_handle_t *queue_handle, uint32_t local_head)
{
    uint32_t current_length = serial_queue_length(queue_handle);
    uint32_t new_length = queue_handle->queue->tail - local_head;

    /* Ensure updates to head don't corrupt queue or capacity constraints */
    assert(new_length <= current_length);

#ifdef CONFIG_ENABLE_SMP_SUPPORT
    THREAD_MEMORY_RELEASE();
#endif

    queue_handle->queue->head = local_head;
}

/**
 * Return the number of bytes of data stored contiguously in the queue from
 * the head index to either the tail index or the end of the data region.
 *
 * @param queue_handle queue containing the data.
 *
 * @return Number of bytes stored contiguously in the queue.
 */
static inline uint32_t serial_queue_contiguous_length(serial_queue_handle_t *queue_handle)
{
    return MIN(queue_handle->capacity - (queue_handle->queue->head % queue_handle->capacity),
               serial_queue_length(queue_handle));
}

/**
 * Return the number of free bytes remaining in the queue. This is the number of
 * bytes that can be enqueued until the queue is full.
 *
 * @param queue_handle queue to be filled with data.
 *
 * @return The amount of free space remaining in the queue.
 */
static inline uint32_t serial_queue_free(serial_queue_handle_t *queue_handle)
{
    return queue_handle->capacity - serial_queue_length(queue_handle);
}

/**
 * Return the number of bytes that can be copied into the queue contiguously. This
 * is the number of bytes that can be copied into the queue with a single call of memcpy.
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
 * Enqueue a buffer of contiguous characters into a queue.
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

    sddf_memcpy(dst, src, num_prewrap);
    if (num_postwrap) {
        sddf_memcpy(queue_handle->data_region, src + num_prewrap, num_postwrap);
    }

    serial_update_shared_tail(queue_handle, queue_handle->queue->tail + num);

    return num;
}

/**
 * Transfer all data from a consumer queue to a producer queue. Assumes there
 * is enough free space in the free queue to fit all data in the active
 * queue.
 *
 * @param free_queue_handle queue to produce into.
 * @param active_queue_handle queue to consume.
 */
static inline void serial_transfer_all(serial_queue_handle_t *free_queue_handle,
                                       serial_queue_handle_t *active_queue_handle)
{
    assert(serial_queue_length(active_queue_handle) <= serial_queue_free(free_queue_handle));

    /* Copy in contiguous chunks */
    while (serial_queue_length(active_queue_handle)) {
        uint32_t num_active = serial_queue_contiguous_length(active_queue_handle);
        char *src = active_queue_handle->data_region
                  + (active_queue_handle->queue->head % active_queue_handle->capacity);

        uint32_t transferred = serial_enqueue_batch(free_queue_handle, num_active, src);
        assert(transferred == num_active);

        serial_update_shared_head(active_queue_handle, active_queue_handle->queue->head + num_active);
    }
}

/**
 * Transfer all data from a consumer queue to a producer queue, adding colour codes
 * before and after. Assumes there is enough free space in the free queue to fit
 * all data in the active.
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
    assert(serial_queue_length(active_queue_handle) + col_start_len + col_end_len
           <= serial_queue_free(free_queue_handle));

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
