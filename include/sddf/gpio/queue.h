/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sddf/util/fence.h>

/*
 * Here we choose the default data size and queue entries. This means
 * that by default the data region would need 4KiB of space (1 page on
 * AArch64 for example). These defaults have worked for our example systems
 * but are left configurable for the system designer if they are too small.
 */

#ifndef NUM_QUEUE_ENTRIES
#define NUM_QUEUE_ENTRIES 4000
#endif

typedef struct gpio_irq_queue_entry {
    /* Channel id associated with the IRQ */
    uint8_t channel_id;
} gpio_irq_queue_entry_t;

/* Shared queue structure that contains irqs forwarded from driver */
typedef struct gpio_irq_queue {
    uint32_t tail;
    uint32_t head;
    gpio_irq_queue_entry_t entries[NUM_QUEUE_ENTRIES];
} gpio_irq_queue_t;

/* Convenience struct for storing request and response queues */
typedef struct gpio_irq_queue_handle {
    gpio_irq_queue_t *notifications;
} gpio_irq_queue_handle_t;

/**
 * Initialise the queue.
 * Note that this assumes that the request and response queues are zero-initalised.
 *
 * @param queue queue handle to use.
 * @param notifications pointer to notifications queue in shared memory.
 */
static inline gpio_irq_queue_handle_t gpio_irq_queue_init(gpio_irq_queue_t *notifications)
{
    gpio_irq_queue_handle_t handle;
    handle.notifications = notifications;
    return handle;
}

/**
 * Check if the queue is empty.
 *
 * @param queue queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline int gpio_irq_queue_empty(gpio_irq_queue_t *queue)
{
    return queue->tail - queue->head == 0;
}

/**
 * Check if the queue is full
 *
 * @param queue queue to check.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int gpio_irq_queue_full(gpio_irq_queue_t *queue)
{
    return queue->tail - queue->head + 1 == NUM_QUEUE_ENTRIES;
}

/**
 * Get the number of entries in a queue
 *
 * @param queue queue to check.
 *
 * @return number of entries in a queue
 */
static inline uint32_t gpio_irq_queue_length(gpio_irq_queue_t *queue)
{
    return (queue->tail - queue->head);
}

/**
 * Enqueue an element into the notification queue
 *
 * @param queue queue handle to enqueue into.
 * @param channel_id channel id of notification to enqueue
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int gpio_irq_enqueue_notification(gpio_irq_queue_handle_t h, uint8_t channel_id)
{
    if (gpio_irq_queue_full(h.notifications)) {
        return -1;
    }

    size_t index = h.notifications->tail % NUM_QUEUE_ENTRIES;
    h.notifications->entries[index].channel_id = channel_id;

    THREAD_MEMORY_RELEASE();
    h.notifications->tail++;

    return 0;
}

/**
 * Dequeue an element from the notification queue
 *
 * @param queue queue handle to dequeue from
 * @param channel_id channel id of dequeued notification
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int gpio_irq_dequeue_notification(gpio_irq_queue_handle_t h, uint8_t *channel_id)
{
    if (gpio_irq_queue_empty(h.notifications)) {
        return -1;
    }

    size_t index = h.notifications->head % NUM_QUEUE_ENTRIES;
    *channel_id = h.notifications->entries[index].channel_id;

    THREAD_MEMORY_RELEASE();
    h.notifications->head++;

    return 0;
}
