/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/serial/queue.h>

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

int serial_queue_empty(serial_queue_t *queue)
{
    return !((queue->tail - queue->head) % queue->size);
}

int serial_queue_full(serial_queue_t *queue)
{
    // assert((queue->tail - queue->head) >= 0);
    return !((queue->tail - queue->head + 1) % queue->size);
}

uint32_t serial_queue_size(serial_queue_t *queue)
{
    // assert((queue->tail - queue->head) >= 0);
    return (queue->tail - queue->head);
}

int serial_enqueue(serial_queue_t *queue, uintptr_t buffer, unsigned int len)
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

int serial_dequeue(serial_queue_t *queue, uintptr_t *addr, unsigned int *len)
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

int serial_enqueue_free(serial_queue_handle_t *queue, uintptr_t addr, unsigned int len)
{
    // assert(addr);
    return serial_enqueue(queue->free, addr, len);
}

int serial_enqueue_active(serial_queue_handle_t *queue, uintptr_t addr, unsigned int len)
{
    // assert(addr);
    return serial_enqueue(queue->active, addr, len);
}

int serial_dequeue_free(serial_queue_handle_t *queue, uintptr_t *addr, unsigned int *len)
{
    return serial_dequeue(queue->free, addr, len);
}

int serial_dequeue_active(serial_queue_handle_t *queue, uintptr_t *addr, unsigned int *len)
{
    return serial_dequeue(queue->active, addr, len);
}

void serial_queue_plug(serial_queue_t *queue) {
    queue->plugged = true;
}

void serial_queue_unplug(serial_queue_t *queue) {
    queue->plugged = false;
}

bool serial_queue_plugged(serial_queue_t *queue) {
    return queue->plugged;
}
