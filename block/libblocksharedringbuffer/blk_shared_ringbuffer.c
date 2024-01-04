/*
 * Copyright 2023, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <sddf/block/blk_shared_ringbuffer.h>

void blk_ring_init(blk_ring_handle_t *ring_handle,
                        blk_cmd_ring_buffer_t *command,
                        blk_resp_ring_buffer_t *response,
                        int buffer_init,
                        uint32_t command_size,
                        uint32_t response_size)
{
    ring_handle->cmd_ring = command;
    ring_handle->resp_ring = response;
    if (buffer_init) {
        ring_handle->cmd_ring->write_idx = 0;
        ring_handle->cmd_ring->read_idx = 0;
        ring_handle->cmd_ring->size = command_size;
        ring_handle->cmd_ring->plugged = false;
        
        ring_handle->resp_ring->write_idx = 0;
        ring_handle->resp_ring->read_idx = 0;
        ring_handle->resp_ring->size = response_size;
    }
}