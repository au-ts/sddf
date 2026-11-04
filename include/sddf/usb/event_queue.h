/*
 * Copyright 2022, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <host/hcd.h>

/**
 * The event queue, like all sDDF queues, is an implementation of a
 * single-producer, single-consumer FIFO queue. The key assumption being that
 * only the producer is permitted to modify the tail, and only the consumer is
 * permitted to modify the head. Both components are permitted to read both
 * indices. The library's atomic operations are written to ensure correctness
 * under these assumptions, thus each function's description contains an
 * explicit notes on its assumed caller.
 */

typedef struct event_queue {
    /* index to insert at */
    uint32_t tail;
    /* index to remove from */
    uint32_t head;
    /* flag to indicate whether producer requires signalling */
    uint32_t producer_signalled;
} event_queue_t;

typedef struct event_queue_handle {
    event_queue_t *queue;
    uint32_t capacity;
    hcd_event_t *data_region;
} event_queue_handle_t;

/**
 * Return the number of events stored in the queue. This is calculated by using
 * the head and tail values currently stored in the shared queue handle data
 * structure. This function should only be called by the CONSUMER of the queue.
 *
 * @param queue_handle queue containing the data.
 *
 * @return The number of events stored in the queue.
 */
static inline uint32_t event_queue_length_consumer(event_queue_handle_t *queue_handle)
{
    /* The load-acquire will be paired with the store-release
     * in event_enqueue() or event_update_shared_tail().
     */
    uint32_t tail = load_acquire_32(&queue_handle->queue->tail);
    uint32_t head = queue_handle->queue->head;
    return (tail - head);
}

/**
 * Return the number of events stored in the queue. This is calculated by using
 * the head and tail values currently stored in the shared queue handle data
 * structure. This function should only be called by the PRODUCER of the queue.
 *
 * @param queue_handle queue containing the data.
 *
 * @return The number bytes of data stored in the queue.
 */
static inline uint32_t event_queue_length_producer(event_queue_handle_t *queue_handle)
{
    uint32_t tail = queue_handle->queue->tail;
    /* The load-acquire will be paired with the store-release
     * in event_dequeue() or event_update_shared_head().
     */
    uint32_t head = load_acquire_32(&queue_handle->queue->head);
    return (tail - head);
}

/**
 * Check if the queue is empty. This function should only be called by the
 * CONSUMER of the queue.
 *
 * @param queue_handle queue to check.
 * @param local_head head which points to the next event to be dequeued.
 * Should be set to the value of the shared head in the queue if a local copy is
 * not in use.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline int event_queue_empty(event_queue_handle_t *queue_handle, uint32_t local_head)
{
    /* The load-acquire will be paired with the store-release
     * in event_enqueue() or event_update_shared_tail().
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
static inline int event_queue_full(event_queue_handle_t *queue_handle, uint32_t local_tail)
{
    /* The load-acquire will be paired with the store-release
     * in event_dequeue() or event_update_shared_head().
     */
    uint32_t head = load_acquire_32(&queue_handle->queue->head);

    return local_tail - head == queue_handle->capacity;
}

/**
 * Enqueue an event into a queue. Update the shared tail so the event is visible
 * to the consumer. This function should only be called by the PRODUCER of the
 * queue.
 *
 * @param queue_handle queue to enqueue into.
 * @param event event to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int event_enqueue(event_queue_handle_t *queue_handle, hcd_event_t event)
{
    uint32_t *tail = &queue_handle->queue->tail;

    if (event_queue_full(queue_handle, *tail)) {
        return -1;
    }

    queue_handle->data_region[*tail % queue_handle->capacity] = event;

    /* The store-release will synchronise with load-acquires by the CONSUMER of the queue. */
    store_release_32(tail, *tail + 1);

    return 0;
}

/**
 * Enqueue an event locally into a queue. Update a local tail variable so the
 * event is not visible to the consumer. This function should only be called
 * by the PRODUCER of the queue.
 *
 * @param queue_handle queue to enqueue into.
 * @param local_tail address of the tail to be used and incremented.
 * @param event event to be enqueued.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int event_enqueue_local(event_queue_handle_t *queue_handle, uint32_t *local_tail, hcd_event_t event)
{
    if (event_queue_full(queue_handle, *local_tail)) {
        return -1;
    }

    queue_handle->data_region[*local_tail % queue_handle->capacity] = event;
    (*local_tail)++;

    return 0;
}

/**
 * Dequeue an event from a queue. Update the shared head so the removal of the
 * event is visible to the producer. This function should only be called by the
 * CONSUMER of the queue.
 *
 * @param queue_handle queue to dequeue from.
 * @param event address of event to copy into.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int event_dequeue(event_queue_handle_t *queue_handle, hcd_event_t *event)
{
    uint32_t *head = &queue_handle->queue->head;

    if (event_queue_empty(queue_handle, *head)) {
        return -1;
    }

    *event = queue_handle->data_region[*head % queue_handle->capacity];

    /* The store-release will synchronise with load-acquires by the PRODUCER of the queue. */
    store_release_32(head, *head + 1);

    return 0;
}

/**
 * Dequeue an event locally from a queue. Update a local head variable so the
 * removal of the event is not visible to the producer. This function should
 * only be called by the CONSUMER of the queue.
 *
 * @param queue_handle queue to dequeue from.
 * @param local_head address of the head to be used and incremented.
 * @param event event to copy into.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int event_dequeue_local(event_queue_handle_t *queue_handle, uint32_t *local_head, hcd_event_t *event)
{
    if (event_queue_empty(queue_handle, *local_head)) {
        return -1;
    }

    *event = queue_handle->data_region[*local_head % queue_handle->capacity];
    (*local_head)++;

    return 0;
}

/**
 * Update the value of the tail in the shared data structure to make locally
 * enqueued data visible. This function should only be called by the PRODUCER of
 * the queue.
 *
 * @param queue_handle queue to update.
 * @param local_tail tail which points to the last event enqueued.
 */
static inline void event_update_shared_tail(event_queue_handle_t *queue_handle, uint32_t local_tail)
{
#ifdef CONFIG_DEBUG_BUILD
    /* The load-acquire will be paired with the store-release
     * in event_dequeue() or event_update_shared_head().
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
 * @param local_head head which points to the next event to dequeue.
 */
static inline void event_update_shared_head(event_queue_handle_t *queue_handle, uint32_t local_head)
{
#ifdef CONFIG_DEBUG_BUILD
    /* The load-acquire will be paired with the store-release
     * in event_enqueue() or event_update_shared_tail().
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
 * Return the number of events stored contiguously in the queue from the head
 * index to either the tail index or the end of the data region. This function
 * should only be called by the CONSUMER of the queue.
 *
 * @param queue_handle queue containing the data.
 *
 * @return Number of events stored contiguously in the queue.
 */
static inline uint32_t event_queue_contiguous_length(event_queue_handle_t *queue_handle)
{
    uint32_t head = queue_handle->queue->head;
    uint32_t length = event_queue_length_consumer(queue_handle);

    return MIN(queue_handle->capacity - (head % queue_handle->capacity), length);
}

/**
 * Return the number of free slots remaining in the queue. This is the number of
 * events that can be enqueued until the queue is full. This function should
 * only be called by the PRODUCER of the queue.
 *
 * @param queue_handle queue to be filled with data.
 *
 * @return The amount of free space remaining in the queue.
 */
static inline uint32_t event_queue_free(event_queue_handle_t *queue_handle)
{
    uint32_t length = event_queue_length_producer(queue_handle);

    return (queue_handle->capacity - length);
}

/**
 * Return the number of events that can be copied into the queue contiguously.
 * This is the number of eventse that can be copied into the queue with a single
 * call of memcpy. This function should only be called by the PRODUCER of the
 * queue.
 *
 * @param queue_handle queue to be filled with data.
 *
 * @return The amount of contiguous free space remaining in the queue.
 */
static inline uint32_t event_queue_contiguous_free(event_queue_handle_t *queue_handle)
{
    return MIN(queue_handle->capacity - (queue_handle->queue->tail % queue_handle->capacity),
               event_queue_free(queue_handle));
}

/**
 * Initialise the queue handle data structure with the shared queue.
 *
 * @param queue_handle queue handle to use.
 * @param queue pointer to queue in shared memory.
 * @param capacity capacity of the queue.
 * @param data_region address of the data region.
 */
static inline void event_queue_init(event_queue_handle_t *queue_handle, event_queue_t *queue, uint32_t capacity,
                                    hcd_event_t *data_region)
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
static inline void event_request_consumer_signal(event_queue_handle_t *queue_handle)
{
    store_relaxed_32(&queue_handle->queue->producer_signalled, 0);
    /* The sc fence will synchronise with the sc fence in the consumer in the signalling protocol,
     * such that at least one of the producer and the consumer can make progress
     * and avoid deadlock.
     *
     * More information on the sDDF signalling protocol can be found in the corresponding section
     * in the developer docs (docs/developing.md).
     *
     * The sc fence ensures that:
     * 1. The producer is observed to set the `producer_signalled` flag before performing its
     *    "re-check" of the space in the queue.
     * 2. The consumer is observed to check the producer_signalled flag after it terminates updating
     *    the queue.
     * Enforcing the ordering of these events ensures that the producer will not become deadlocked
     * awaiting free space in the queue (assuming this space does become available).
     *
     * Once the producer breaks out of its queue processing loop, if the consumer subsequently
     * makes space available there are two possible timelines:
     * 1. The producer's update to the flag is observed by the consumer, causing the consumer to
     *    notify.
     * 2. The producer's update to the flag is not observed, thus must not have occurred at the time
     *    of the consumer's decision to notify. If this is the case then the producer's "re-check"
     *    also hasn't occurred (thanks to the fences). Thus, when this "re-check" is performed the
     *    free space in the queue will be observable (thanks again to the fences), triggering the
     *    producer to "re-process" the queue.
     *
     * From a memory model perspective, the following shape of cppmem program
     * (http://svr-pes20-cppmem.cl.cam.ac.uk/cppmem/) represents the undesired behaviour that is
     * prevented by the pair of sc fences.
     *
     * int main() {
     *   atomic_int flag = 0;
     *   atomic_int queue = 0;
     *   {{{
     *     // producer
     *     {
     *       flag.store(1, relaxed);
     *       atomic_thread_fence(seq_cst);
     *       queue.load(relaxed).readsvalue(0);
     *     }
     *   |||
     *     // consumer
     *     {
     *       queue.store(1, relaxed);
     *       atomic_thread_fence(seq_cst);
     *       flag.load(relaxed).readsvalue(0);
     *     }
     *   }}};
     * }
     */
    fence_seq_cst();
}

/**
 * Indicate that producer has been signalled.
 *
 * @param queue queue handle of the queue that has been signalled.
 */
static inline void event_cancel_consumer_signal(event_queue_handle_t *queue_handle)
{
    store_relaxed_32(&queue_handle->queue->producer_signalled, 1);
    /* It is not necessary to insert a sc fence here, unlike in event_request_consumer_signal(),
     * as the signalling protocol requires that a cancellation is always followed by a request.
     */
}

/**
 * Producer of the queue requires signalling.
 *
 * @param queue queue handle of the queue to check.
 */
static inline bool event_require_consumer_signal(event_queue_handle_t *queue_handle)
{
    /* The sc fence will synchronise with the sc fence in the producer in the signalling protocol,
     * such that at least one of the producer and the consumer can make progress
     * and avoid deadlock.
     */
    fence_seq_cst();
    return !load_relaxed_32(&queue_handle->queue->producer_signalled);
}
