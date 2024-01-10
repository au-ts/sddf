/*
 * Copyright 2023, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <sddf/block/blk_shared_ringbuffer.h>

void blk_ring_init(blk_ring_handle_t *ring_handle,
                        blk_req_ring_buffer_t *request,
                        blk_resp_ring_buffer_t *response,
                        int buffer_init,
                        uint32_t request_size,
                        uint32_t response_size)
{
    ring_handle->req_ring = request;
    ring_handle->resp_ring = response;
    if (buffer_init) {
        ring_handle->req_ring->write_idx = 0;
        ring_handle->req_ring->read_idx = 0;
        ring_handle->req_ring->size = request_size;
        ring_handle->req_ring->plugged = false;
        
        ring_handle->resp_ring->write_idx = 0;
        ring_handle->resp_ring->read_idx = 0;
        ring_handle->resp_ring->size = response_size;
    }
}