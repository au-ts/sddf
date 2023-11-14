/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "shared_ringbuffer.h"

void blk_ring_init(blk_ring_handle_t *ring,
                blk_cmd_ring_buffer_t *command,
                blk_resp_ring_buffer_t *response,
                blk_data_ring_buffer_t *data,
                int buffer_init,
                uint32_t command_size,
                uint32_t response_size,
                uint32_t data_size)
{
    ring->cmd_ring = command;
    ring->resp_ring = response;
    ring->data_ring = data;
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
        ring->data_ring->write_idx = 0;
        ring->data_ring->read_idx = 0;
        ring->data_ring->size = data_size;
    }
}
