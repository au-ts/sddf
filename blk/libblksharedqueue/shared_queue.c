/*
 * Copyright 2023, UNSW
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

bool blk_req_queue_empty(blk_queue_handle_t *h)
{
    return !((h->req_queue->write_idx - h->req_queue->read_idx) % h->req_queue->size);
}

bool blk_resp_queue_empty(blk_queue_handle_t *h)
{
    return !((h->resp_queue->write_idx - h->resp_queue->read_idx) % h->resp_queue->size);
}

bool blk_req_queue_full(blk_queue_handle_t *h)
{
    return !((h->req_queue->write_idx - h->req_queue->read_idx + 1) % h->req_queue->size);
}

bool blk_resp_queue_full(blk_queue_handle_t *h)
{
    return !((h->resp_queue->write_idx - h->resp_queue->read_idx + 1) % h->resp_queue->size);
}

int blk_req_queue_size(blk_queue_handle_t *h)
{
    return (h->req_queue->write_idx - h->req_queue->read_idx);
}

int blk_resp_queue_size(blk_queue_handle_t *h)
{
    return (h->resp_queue->write_idx - h->resp_queue->read_idx);
}

int blk_enqueue_req(blk_queue_handle_t *h,
                                        blk_request_code_t code,
                                        uintptr_t addr,
                                        uint32_t block_number,
                                        uint16_t count,
                                        uint32_t id)
{
    if (blk_req_queue_full(h)) {
        return -1;
    }

    h->req_queue->buffers[h->req_queue->write_idx % h->req_queue->size].code = code;
    h->req_queue->buffers[h->req_queue->write_idx % h->req_queue->size].addr = addr;
    h->req_queue->buffers[h->req_queue->write_idx % h->req_queue->size].block_number = block_number;
    h->req_queue->buffers[h->req_queue->write_idx % h->req_queue->size].count = count;
    h->req_queue->buffers[h->req_queue->write_idx % h->req_queue->size].id = id;

    THREAD_MEMORY_RELEASE();
    h->req_queue->write_idx++;

    return 0;
}

int blk_enqueue_resp(blk_queue_handle_t *h,
                                    blk_response_status_t status,
                                    uintptr_t addr,
                                    uint16_t count,
                                    uint16_t success_count,
                                    uint32_t id)
{
    if (blk_resp_queue_full(h)) {
        return -1;
    }

    h->resp_queue->buffers[h->resp_queue->write_idx % h->resp_queue->size].status = status;
    h->resp_queue->buffers[h->resp_queue->write_idx % h->resp_queue->size].addr = addr;
    h->resp_queue->buffers[h->resp_queue->write_idx % h->resp_queue->size].count = count;
    h->resp_queue->buffers[h->resp_queue->write_idx % h->resp_queue->size].success_count = success_count;
    h->resp_queue->buffers[h->resp_queue->write_idx % h->resp_queue->size].id = id;

    THREAD_MEMORY_RELEASE();
    h->resp_queue->write_idx++;

    return 0;
}

int blk_dequeue_req(blk_queue_handle_t *h,
                    blk_request_code_t *code,
                    uintptr_t *addr,
                    uint32_t *block_number,
                    uint16_t *count,
                    uint32_t *id)
{
    if (blk_req_queue_empty(h)) {
        return -1;
    }

    *code = h->req_queue->buffers[h->req_queue->read_idx % h->req_queue->size].code;
    *addr = h->req_queue->buffers[h->req_queue->read_idx % h->req_queue->size].addr;
    *block_number = h->req_queue->buffers[h->req_queue->read_idx % h->req_queue->size].block_number;
    *count = h->req_queue->buffers[h->req_queue->read_idx % h->req_queue->size].count;
    *id = h->req_queue->buffers[h->req_queue->read_idx % h->req_queue->size].id;

    THREAD_MEMORY_RELEASE();
    h->req_queue->read_idx++;

    return 0;
}

int blk_dequeue_resp(blk_queue_handle_t *h,
                        blk_response_status_t *status,
                        uintptr_t *addr,
                        uint16_t *count,
                        uint16_t *success_count,
                        uint32_t *id)
{
    if (blk_resp_queue_empty(h)) {
        return -1;
    }

    *status = h->resp_queue->buffers[h->resp_queue->read_idx % h->resp_queue->size].status;
    *addr = h->resp_queue->buffers[h->resp_queue->read_idx % h->resp_queue->size].addr;
    *count = h->resp_queue->buffers[h->resp_queue->read_idx % h->resp_queue->size].count;
    *success_count = h->resp_queue->buffers[h->resp_queue->read_idx % h->resp_queue->size].success_count;
    *id = h->resp_queue->buffers[h->resp_queue->read_idx % h->resp_queue->size].id;

    THREAD_MEMORY_RELEASE();
    h->resp_queue->read_idx++;

    return 0;
}

void blk_req_queue_plug(blk_queue_handle_t *h)
{
    h->req_queue->plugged = true;
}

void blk_req_queue_unplug(blk_queue_handle_t *h)
{
    h->req_queue->plugged = false;
}

bool blk_req_queue_plugged(blk_queue_handle_t *h)
{
    return h->req_queue->plugged;
}
