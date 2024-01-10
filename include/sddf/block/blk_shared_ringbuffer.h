/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include "fence.h"

/* Number of buffers the request ring is configured to have. */
#define BLK_NUM_REQ_BUFFERS 1024
/* Number of buffers the response ring is configured to have. */
#define BLK_NUM_RESP_BUFFERS 1024

typedef struct blk_storage_info {
    char serial_number[64];
    bool read_only;
    bool ready;
    uint16_t blocksize;
    uint16_t queue_depth;
    uint16_t cylinders, heads, blocks; /* geometry to guide FS layout */
    uint64_t size; /* number of blocksize units */
} blk_storage_info_t;

/* Request code for block */
typedef enum blk_request_code {
    BLK_REQUEST_READ,
    BLK_REQUEST_WRITE,
    BLK_REQUEST_FLUSH,
    BLK_REQUEST_BARRIER,
} blk_request_code_t;

/* Response status for block */
typedef enum blk_response_status {
    BLK_RESPONSE_OK,
    BLK_RESPONSE_ERROR,
} blk_response_status_t;

/* Request struct contained in request ring */
typedef struct blk_request {
    blk_request_code_t code; /* request code */
    uintptr_t addr; /*  */
    uint32_t sector; /* sector number to read/write */
    uint16_t count; /* number of blocks to read/write */
    uint32_t id; /* stores request ID */
} blk_request_t;

/* Response struct contained in response ring */
typedef struct blk_response {
    blk_response_status_t status; /* response status */
    uintptr_t addr; /* encoded dma address of data */
    uint16_t count; /* number of blocks allocated for corresponding request */
    uint16_t success_count; /* number of blocks successfully read/written */
    uint32_t id; /* stores corresponding request ID */
} blk_response_t;

/* Circular buffer containing requests */
typedef struct blk_req_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size; /* number of buffers in request ring buffer */
    bool plugged; /* prevent requests from being dequeued when plugged */
    blk_request_t buffers[BLK_NUM_REQ_BUFFERS];
} blk_req_ring_buffer_t;

/* Circular buffer containing responses */
typedef struct blk_resp_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size; /* number of buffers in response ring buffer */
    blk_response_t buffers[BLK_NUM_RESP_BUFFERS];
} blk_resp_ring_buffer_t;

/* A ring handle for queueing/dequeueing request and responses */
typedef struct blk_ring_handle {
    blk_req_ring_buffer_t *req_ring;
    blk_resp_ring_buffer_t *resp_ring;
} blk_ring_handle_t;

/**
 * Initialise the shared ring buffer.
 *
 * @param ring_handle ring handle to use.
 * @param request pointer to request ring in shared memory.
 * @param response pointer to response ring in shared memory.
 * @param buffer_init 1 indicates the read and write indices in shared memory need to be initialised.
 *                    0 indicates they do not. Only one side of the shared memory regions needs to do this.
 * @param request_size number of buffers in request ring.
 * @param response_size number of buffers in response ring.
 */
void blk_ring_init(blk_ring_handle_t *ring_handle,
                        blk_req_ring_buffer_t *request,
                        blk_resp_ring_buffer_t *response,
                        int buffer_init,
                        uint32_t request_size,
                        uint32_t response_size);

/**
 * Check if the request ring buffer is empty.
 *
 * @param ring_handle ring handle containing request ring buffer.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline bool blk_req_ring_empty(blk_ring_handle_t *ring_handle)
{
    return !((ring_handle->req_ring->write_idx - ring_handle->req_ring->read_idx) % ring_handle->req_ring->size);
}

/**
 * Check if the response ring buffer is empty.
 *
 * @param ring_handle ring handle containing response ring buffer.
 *
 * @return true indicates the response ring buffer is empty, false otherwise.
 */
static inline bool blk_resp_ring_empty(blk_ring_handle_t *ring_handle)
{
    return !((ring_handle->resp_ring->write_idx - ring_handle->resp_ring->read_idx) % ring_handle->resp_ring->size);
}

/**
 * Check if the request ring buffer is full.
 *
 * @param ring_handle ring handle containing request ring buffer.
 *
 * @return true indicates the request ring buffer is full, false otherwise.
 */
static inline bool blk_req_ring_full(blk_ring_handle_t *ring_handle)
{
    return !((ring_handle->req_ring->write_idx - ring_handle->req_ring->read_idx + 1) % ring_handle->req_ring->size);
}

/**
 * Check if the response ring buffer is full.
 *
 * @param ring_handle ring handle containing response ring buffer.
 *
 * @return true indicates the response ring buffer is full, false otherwise.
 */
static inline bool blk_resp_ring_full(blk_ring_handle_t *ring_handle)
{
    return !((ring_handle->resp_ring->write_idx - ring_handle->resp_ring->read_idx + 1) % ring_handle->resp_ring->size);
}

/**
 * Get the number of elements in a request ring buffer.
 *
 * @param ring_handle ring handle containing request and response ring buffers.
 *
 * @return number of elements in the ring buffer.
 */
static inline int blk_req_ring_size(blk_ring_handle_t *ring_handle)
{
    return (ring_handle->req_ring->write_idx - ring_handle->req_ring->read_idx);
}

/**
 * Get the number of elements in a response ring buffer.
 *
 * @param ring_handle ring handle containing request and response ring buffers.
 *
 * @return number of elements in the ring buffer.
 */
static inline int blk_resp_ring_size(blk_ring_handle_t *ring_handle)
{
    return (ring_handle->resp_ring->write_idx - ring_handle->resp_ring->read_idx);
}

/**
 * Enqueue an element into the request ring buffer.
 *
 * @param ring_handle Ring handle containing request ring to enqueue to.
 * @param code request code.
 * @param addr encoded dma address of data to read/write.
 * @param sector sector number to read/write.
 * @param count the number of sectors to read/write
 * @param id request ID to identify this request.
 *
 * @return -1 when request ring is full, 0 on success.
 */
static inline int blk_enqueue_req(blk_ring_handle_t *ring_handle,
                                        blk_request_code_t code,
                                        uintptr_t addr,
                                        uint32_t sector,
                                        uint16_t count,
                                        uint32_t id)
{
    if (blk_req_ring_full(ring_handle)) {
        return -1;
    }

    ring_handle->req_ring->buffers[ring_handle->req_ring->write_idx % ring_handle->req_ring->size].code = code;
    ring_handle->req_ring->buffers[ring_handle->req_ring->write_idx % ring_handle->req_ring->size].addr = addr;
    ring_handle->req_ring->buffers[ring_handle->req_ring->write_idx % ring_handle->req_ring->size].sector = sector;
    ring_handle->req_ring->buffers[ring_handle->req_ring->write_idx % ring_handle->req_ring->size].count = count;
    ring_handle->req_ring->buffers[ring_handle->req_ring->write_idx % ring_handle->req_ring->size].id = id;

    THREAD_MEMORY_RELEASE();
    ring_handle->req_ring->write_idx++;

    return 0;
}

/**
 * Enqueue an element into the response ring buffer.
 * This indicates the request has been processed and a response is ready.
 *
 * @param ring_handle Ring handle containing response ring to enqueue to.
 * @param status response status.
 * @param addr pointer to encoded dma address of data.
 * @param count number of sectors allocated for corresponding request
 * @param success_count number of sectors successfully read/written
 * @param id request ID to identify which request the response is for.
 *
 * @return -1 when response ring is full, 0 on success.
 */
static inline int blk_enqueue_resp(blk_ring_handle_t *ring_handle,
                                        blk_response_status_t status,
                                        uintptr_t addr,
                                        uint16_t count,
                                        uint16_t success_count,
                                        uint32_t id)
{
    if (blk_resp_ring_full(ring_handle)) {
        return -1;
    }

    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].status = status;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].addr = addr;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].count = count;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].success_count = success_count;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].id = id;

    THREAD_MEMORY_RELEASE();
    ring_handle->resp_ring->write_idx++;

    return 0;
}

/**
 * Dequeue an element from the request ring buffer.
 *
 * @param ring Ring handle containing request ring to dequeue from.
 * @param code pointer to request code.
 * @param addr pointer to encoded dma address of data.
 * @param sector pointer to  sector number to read/write.
 * @param count pointer to number of sectors to read/write.
 * @param id pointer to store request ID.
 *
 * @return -1 when request ring is empty, 0 on success.
 */
static inline int blk_dequeue_req(blk_ring_handle_t *ring_handle,
                                        blk_request_code_t *code,
                                        uintptr_t *addr,
                                        uint32_t *sector,
                                        uint16_t *count,
                                        uint32_t *id)
{
    if (blk_req_ring_empty(ring_handle)) {
        return -1;
    }

    *code = ring_handle->req_ring->buffers[ring_handle->req_ring->read_idx % ring_handle->req_ring->size].code;
    *addr = ring_handle->req_ring->buffers[ring_handle->req_ring->read_idx % ring_handle->req_ring->size].addr;
    *sector = ring_handle->req_ring->buffers[ring_handle->req_ring->read_idx % ring_handle->req_ring->size].sector;
    *count = ring_handle->req_ring->buffers[ring_handle->req_ring->read_idx % ring_handle->req_ring->size].count;
    *id = ring_handle->req_ring->buffers[ring_handle->req_ring->read_idx % ring_handle->req_ring->size].id;

    THREAD_MEMORY_RELEASE();
    ring_handle->req_ring->read_idx++;

    return 0;
}

/**
 * Dequeue an element from a response ring buffer.
 *
 * @param ring Ring handle containing response ring to dequeue from.
 * @param status pointer to response status.
 * @param addr pointer to encoded dma address of data.
 * @param count pointer to number of sectors allocated for corresponding request
 * @param success_count pointer to number of sectors successfully read/written
 * @param id pointer to storing request ID to idenfity which request this response is for.
 * @return -1 when response ring is empty, 0 on success.
 */
static inline int blk_dequeue_resp(blk_ring_handle_t *ring_handle,
                                        blk_response_status_t *status,
                                        uintptr_t *addr,
                                        uint16_t *count,
                                        uint16_t *success_count,
                                        uint32_t *id)
{
    if (blk_resp_ring_empty(ring_handle)) {
        return -1;
    }

    *status = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].status;
    *addr = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].addr;
    *count = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].count;
    *success_count = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].success_count;
    *id = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].id;

    THREAD_MEMORY_RELEASE();
    ring_handle->resp_ring->read_idx++;

    return 0;
}

/**
 * Set the plug of the request ring to true.
 *
 * @param ring_handle Ring handle containing request ring to check for plug.
*/
static inline void blk_req_ring_plug(blk_ring_handle_t *ring_handle) {
    ring_handle->req_ring->plugged = true;
}

/**
 * Set the plug of the request ring to false.
 *
 * @param ring Ring handle containing request ring to check for plug.
*/
static inline void blk_req_ring_unplug(blk_ring_handle_t *ring_handle) {
    ring_handle->req_ring->plugged = false;
}

/**
 * Check the current value of the request ring plug.
 *
 * @param ring Ring handle containing request ring to check for plug.
 *
 * @return true when request ring is plugged, false when unplugged.
*/
static inline bool blk_req_ring_plugged(blk_ring_handle_t *ring_handle) {
    return ring_handle->req_ring->plugged;
}

