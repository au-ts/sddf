/*
 * Copyright 2023, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <sddf/block/blk_shared_queue.h>

void blk_queue_init(blk_queue_handle_t *queue_handle,
                        blk_req_queue_t *request,
                        blk_resp_queue_t *response,
                        bool buffer_init,
                        uint32_t request_size,
                        uint32_t response_size)
{
    queue_handle->req_queue = request;
    queue_handle->resp_queue = response;
    if (buffer_init) {
        queue_handle->req_queue->write_idx = 0;
        queue_handle->req_queue->read_idx = 0;
        queue_handle->req_queue->size = request_size;
        queue_handle->req_queue->plugged = false;
        
        queue_handle->resp_queue->write_idx = 0;
        queue_handle->resp_queue->read_idx = 0;
        queue_handle->resp_queue->size = response_size;
    }
}