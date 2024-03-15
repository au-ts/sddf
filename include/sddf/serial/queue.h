/*
 * Copyright 2022, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <sddf/util/fence.h>

/* Number of entries each queue is configured to have. */
#define NUM_ENTRIES 512
/* Size of the data that each queue entry points to. */
#define BUFFER_SIZE 2048

/* Buffer descriptor */
typedef struct serial_queue_entry {
    uintptr_t encoded_addr; /* encoded dma addresses */
    unsigned int len; /* associated memory lengths */
} serial_queue_entry_t;

/* Circular buffer containing descriptors */
typedef struct serial_queue {
    uint32_t tail;
    uint32_t head;
    uint32_t size;
    bool notify_writer;
    bool notify_reader;
    bool plugged;
    serial_queue_entry_t entries[NUM_ENTRIES];
} serial_queue_t;

/* A queue handle for enqueing/dequeuing into  */
typedef struct serial_queue_handle {
    serial_queue_t *free;
    serial_queue_t *active;
} serial_queue_handle_t;

/**
 * Initialise the shared queue structure.
 *
 * @param queue queue handle to use.
 * @param free pointer to free queue in shared memory.
 * @param active pointer to active queue in shared memory.
 * @param buffer_init 1 indicates the head and tail indices in shared memory need to be initialised.
 *                    0 inidicates they do not. Only one side of the shared memory regions needs to do this.
 */
void serial_queue_init(serial_queue_handle_t *queue, serial_queue_t *free, serial_queue_t *active, int buffer_init, uint32_t free_size, uint32_t active_size)
{
    queue->free = free;
    queue->active = active;
    if (buffer_init) {
        queue->free->tail = 0;
        queue->free->head = 0;
        queue->free->size = free_size;
        queue->free->notify_writer = false;
        queue->free->notify_reader = false;
        queue->free->plugged = false;
        queue->active->tail = 0;
        queue->active->head = 0;
        queue->active->size = active_size;
        queue->active->notify_writer =false;
        queue->active->notify_reader = false;
        queue->active->plugged = false;
    }
}

/**
 * Check if the queue is empty.
 *
 * @param queue queue to check.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline int serial_queue_empty(serial_queue_t *queue)
{
    return !((queue->tail - queue->head) % queue->size);
}

/**
 * Check if the queue is full
 *
 * @param queue queue to check.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int serial_queue_full(serial_queue_t *queue)
{
    // assert((queue->tail - queue->head) >= 0);
    return !((queue->tail - queue->head + 1) % queue->size);
}

static inline uint32_t serial_queue_size(serial_queue_t *queue)
{
    // assert((queue->tail - queue->head) >= 0);
    return (queue->tail - queue->head);
}

/**
 * Enqueue an element to a queue
 *
 * @param queue queue to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int serial_enqueue(serial_queue_t *queue, uintptr_t buffer, unsigned int len)
{
    // assert(buffer != 0);
    if (serial_queue_full(queue)) {
        return -1;
    }

    queue->entries[queue->tail % queue->size].encoded_addr = buffer;
    queue->entries[queue->tail % queue->size].len = len;

    THREAD_MEMORY_RELEASE();
    queue->tail++;

    return 0;
}

/**
 * Dequeue an element to a queue.
 *
 * @param queue queue to Dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int serial_dequeue(serial_queue_t *queue, uintptr_t *addr, unsigned int *len)
{
    if (serial_queue_empty(queue)) {
        return -1;
    }

    // assert(queue->entries[queue->head % queue->size].encoded_addr != 0);

    *addr = queue->entries[queue->head % queue->size].encoded_addr;
    *len = queue->entries[queue->head % queue->size].len;

    THREAD_MEMORY_RELEASE();
    queue->head++;

    return 0;
}

/**
 * Enqueue an element into an free queue.
 * This indicates the buffer address parameter is currently free for use.
 *
 * @param queue handle to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int serial_enqueue_free(serial_queue_handle_t *queue, uintptr_t addr, unsigned int len)
{
    // assert(addr);
    return serial_enqueue(queue->free, addr, len);
}

/**
 * Enqueue an element into a active queue.
 * This indicates the buffer address parameter is currently in use.
 *
 * @param queue handle to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int serial_enqueue_active(serial_queue_handle_t *queue, uintptr_t addr, unsigned int len)
{
    // assert(addr);
    return serial_enqueue(queue->active, addr, len);
}

/**
 * Dequeue an element from the free queue.
 *
 * @param queue handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int serial_dequeue_free(serial_queue_handle_t *queue, uintptr_t *addr, unsigned int *len)
{
    return serial_dequeue(queue->free, addr, len);
}

/**
 * Dequeue an element from a active queue.
 *
 * @param queue handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int serial_dequeue_active(serial_queue_handle_t *queue, uintptr_t *addr, unsigned int *len)
{
    return serial_dequeue(queue->active, addr, len);
}

/**
 * Set the plug of a queue to true.
 *
 * @param queue handle to plug.
*/
static inline void serial_queue_plug(serial_queue_t *queue)
{
    queue->plugged = true;
}

/**
 * Set the plug of a queue to false.
 *
 * @param queue handle to unplug.
*/
static inline void serial_queue_unplug(serial_queue_t *queue)
{
    queue->plugged = false;
}

/**
 * Check the current value of the plug.
 *
 * @param queue handle to check plug.
 *
 * @return true when queue is plugged, false when unplugged.
*/
static inline bool serial_queue_plugged(serial_queue_t *queue)
{
    return queue->plugged;
}
