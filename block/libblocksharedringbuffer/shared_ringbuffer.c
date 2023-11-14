/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "shared_ringbuffer.h"

void ring_init(ring_handle_t *ring,
                cmd_ring_buffer_t *command,
                resp_ring_buffer_t *response,
                data_region_t *data_region,
                int buffer_init,
                uint32_t command_size,
                uint32_t response_size,
                uint32_t data_region_size)
{
    ring->cmd_ring = command;
    ring->resp_ring = response;
    ring->data_region = data_region;
    if (buffer_init) {
        ring->cmd_ring->write_idx = 0;
        ring->cmd_ring->read_idx = 0;
        ring->cmd_ring->size = command_size;
        ring->cmd_ring->notify_writer = false;
        ring->cmd_ring->notify_reader = false;
        ring->cmd_ring->plugged = false;
        ring->resp_ring->write_idx = 0;
        ring->resp_ring->read_idx = 0;
        ring->resp_ring->size = response_size;
        ring->resp_ring->notify_writer =false;
        ring->resp_ring->notify_reader = false;
        ring->resp_ring->plugged = false;
        ring->data_region->write_idx = 0;
        ring->data_region->read_idx = 0;
        ring->data_region->size = data_region_size;
    }
}
