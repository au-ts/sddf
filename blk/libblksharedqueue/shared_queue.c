/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <sddf/blk/shared_queue.h>

void blk_queue_init(blk_queue_handle_t *h,
                        blk_req_queue_t *request,
                        blk_resp_queue_t *response,
                        bool buffer_init,
                        uint32_t request_size,
                        uint32_t response_size)
{
    h->req_queue = request;
    h->resp_queue = response;
    if (buffer_init) {
        h->req_queue->write_idx = 0;
        h->req_queue->read_idx = 0;
        h->req_queue->size = request_size;
        h->req_queue->plugged = false;
        h->resp_queue->write_idx = 0;
        h->resp_queue->read_idx = 0;
        h->resp_queue->size = response_size;
    }
}