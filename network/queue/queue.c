/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/network/queue.h>

void net_queue_init(net_queue_handle_t *queue, net_queue_t *free, net_queue_t *used, uint32_t size)
{
    queue->free = free;
    queue->active = used;
    queue->free->size = size;
    queue->active->size = size;
}
