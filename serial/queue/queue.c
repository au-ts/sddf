/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/serial/queue.h>

void serial_queue_init(serial_queue_handle_t *queue, serial_queue_t *free, serial_queue_t *used, int buffer_init, uint32_t free_size, uint32_t used_size)
{
    queue->free = free;
    queue->used = used;
    if (buffer_init) {
        queue->free->write_idx = 0;
        queue->free->read_idx = 0;
        queue->free->size = free_size;
        queue->free->notify_writer = false;
        queue->free->notify_reader = false;
        queue->free->plugged = false;
        queue->used->write_idx = 0;
        queue->used->read_idx = 0;
        queue->used->size = used_size;
        queue->used->notify_writer =false;
        queue->used->notify_reader = false;
        queue->used->plugged = false;
    }
}

int serial_queue_empty(serial_queue_t *queue)
{
    return !((queue->write_idx - queue->read_idx) % queue->size);
}

int serial_queue_full(serial_queue_t *queue)
{
    // assert((queue->write_idx - queue->read_idx) >= 0);
    return !((queue->write_idx - queue->read_idx + 1) % queue->size);
}

uint32_t serial_queue_size(serial_queue_t *queue)
{
    // assert((queue->write_idx - queue->read_idx) >= 0);
    return (queue->write_idx - queue->read_idx);
}

int serial_enqueue(serial_queue_t *queue, uintptr_t buffer, unsigned int len, void *cookie)
{
    // assert(buffer != 0);
    if (serial_queue_full(queue)) {
        return -1;
    }

    queue->entries[queue->write_idx % queue->size].encoded_addr = buffer;
    queue->entries[queue->write_idx % queue->size].len = len;
    queue->entries[queue->write_idx % queue->size].cookie = cookie;

    THREAD_MEMORY_RELEASE();
    queue->write_idx++;

    return 0;
}

int serial_dequeue(serial_queue_t *queue, uintptr_t *addr, unsigned int *len, void **cookie)
{
    if (serial_queue_empty(queue)) {
        return -1;
    }

    // assert(queue->entries[queue->read_idx % queue->size].encoded_addr != 0);

    *addr = queue->entries[queue->read_idx % queue->size].encoded_addr;
    *len = queue->entries[queue->read_idx % queue->size].len;
    *cookie = queue->entries[queue->read_idx % queue->size].cookie;

    THREAD_MEMORY_RELEASE();
    queue->read_idx++;

    return 0;
}

int serial_enqueue_free(serial_queue_handle_t *queue, uintptr_t addr, unsigned int len, void *cookie)
{
    // assert(addr);
    return serial_enqueue(queue->free, addr, len, cookie);
}

int serial_enqueue_used(serial_queue_handle_t *queue, uintptr_t addr, unsigned int len, void *cookie)
{
    // assert(addr);
    return serial_enqueue(queue->used, addr, len, cookie);
}

int serial_dequeue_free(serial_queue_handle_t *queue, uintptr_t *addr, unsigned int *len, void **cookie)
{
    return serial_dequeue(queue->free, addr, len, cookie);
}

int serial_dequeue_used(serial_queue_handle_t *queue, uintptr_t *addr, unsigned int *len, void **cookie)
{
    return serial_dequeue(queue->used, addr, len, cookie);
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

int serial_driver_dequeue(serial_queue_t *queue, uintptr_t *addr, unsigned int *len, void **cookie)
{
    if (serial_queue_empty(queue)) {
        return -1;
    }

    *addr = queue->entries[queue->read_idx % queue->size].encoded_addr;
    *len = queue->entries[queue->read_idx % queue->size].len;
    *cookie = &queue->entries[queue->read_idx % queue->size];

    THREAD_MEMORY_RELEASE();
    queue->read_idx++;

    return 0;
}
