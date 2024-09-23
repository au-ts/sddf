/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/string.h>
#include <sddf/util/fence.h>
#include <sddf/gpu/gpu.h>

typedef enum gpu_req_code {
    /* 2d commands */
    /* Get display info */
    GPU_REQ_GET_DISPLAY_INFO = 0,
    /* Create a blob resource */
    GPU_REQ_RESOURCE_CREATE_BLOB,
    /* Set the scanout of a blob resource */
    GPU_REQ_SET_SCANOUT_BLOB,
    /* Create a regular 2D resource in device */
    GPU_REQ_RESOURCE_CREATE_2D,
    /* Set the scanout of a regular 2D resource */
    GPU_REQ_SET_SCANOUT,
    /* Attach a contiguous memory backing to resource */
    GPU_REQ_RESOURCE_ATTACH_BACKING,
    /* Detach a memory backing from resource */
    GPU_REQ_RESOURCE_DETACH_BACKING,
    /* For regular 2D resources with private memory, transfer data from memory backing to resource private memory */
    GPU_REQ_TRANSFER_TO_2D,
    /* Flushes memory of a resource from device to scanout */
    GPU_REQ_RESOURCE_FLUSH,
    /* Destroy resource in device */
    GPU_REQ_RESOURCE_UNREF,
} gpu_req_code_t;

typedef enum gpu_resp_status {
    /* Success response */
    GPU_RESP_OK = 0,
    /* For misc errors, e.g. attaching backing to a resource that already has backing */
    GPU_RESP_ERR_UNSPEC,
    /* Scanout id does not exist */
    GPU_RESP_ERR_INVALID_SCANOUT_ID,
    /* Resource id does not exist */
    GPU_RESP_ERR_INVALID_RESOURCE_ID,
    /* Specified rectangle is outside the bounds of what is allocated for resource */
    GPU_RESP_ERR_INVALID_BOUNDS,
    /* Invalid parameter in request */
    GPU_RESP_ERR_INVALID_PARAMETER,
} gpu_resp_status_t;

typedef struct gpu_req {
    gpu_req_code_t code;
    /* Request id */
    uint32_t id;
    union {
        gpu_req_get_display_info_t get_display_info;
        gpu_req_resource_create_2d_blob_t resource_create_blob;
        gpu_req_set_scanout_blob_t set_scanout_blob;
        gpu_req_resource_create_2d_t resource_create_2d;
        gpu_req_resource_attach_backing_t resource_attach_backing;
        gpu_req_resource_detach_backing_t resource_detach_backing;
        gpu_req_set_scanout_t set_scanout;
        gpu_req_transfer_to_2d_t transfer_to_2d;
        gpu_req_resource_flush_t resource_flush;
        gpu_req_resource_unref_t resource_unref;
    };
} gpu_req_t;

typedef struct gpu_resp {
    gpu_resp_status_t status;
    /* Stores corresponding request id */
    uint32_t id;
} gpu_resp_t;

/* Circular buffer containing requests */
typedef struct gpu_req_queue {
    uint32_t head;
    uint32_t tail;
    gpu_req_t buffers[];
} gpu_req_queue_t;

/* Circular buffer containing responses */
typedef struct gpu_resp_queue {
    uint32_t head;
    uint32_t tail;
    gpu_resp_t buffers[];
} gpu_resp_queue_t;

typedef struct gpu_queue_handle {
    gpu_req_queue_t *req_queue;
    gpu_resp_queue_t *resp_queue;
    uint32_t capacity;
} gpu_queue_handle_t;

/**
 * Initialise the shared queues.
 *
 * @param h queue handle to use.
 * @param request pointer to request queue in shared memory.
 * @param response pointer to response queue in shared memory.
 * @param capacity number of entries in the req and resp queues.
 */
static inline void gpu_queue_init(gpu_queue_handle_t *h, gpu_req_queue_t *request, gpu_resp_queue_t *response,
                                  uint32_t capacity)
{
    h->req_queue = request;
    h->resp_queue = response;
    h->capacity = capacity;
}

/**
 * Check if the request queue is empty.
 *
 * @param h queue handle containing request queue.
 *
 * @return true indicates the request queue is empty, false otherwise.
 */
static inline bool gpu_queue_empty_req(gpu_queue_handle_t *h)
{
    return h->req_queue->tail - h->req_queue->head == 0;
}

/**
 * Check if the response queue is empty.
 *
 * @param h queue handle containing response queue.
 *
 * @return true indicates the response queue is empty, false otherwise.
 */
static inline bool gpu_queue_empty_resp(gpu_queue_handle_t *h)
{
    return h->resp_queue->tail - h->resp_queue->head == 0;
}

/**
 * Check if the request queue is full.
 *
 * @param h queue handle containing request queue.
 *
 * @return true indicates the request queue is full, false otherwise.
 */
static inline bool gpu_queue_full_req(gpu_queue_handle_t *h)
{
    return h->req_queue->tail - h->req_queue->head + 1 == h->capacity;
}

/**
 * Check if the response queue is full.
 *
 * @param h queue handle containing response queue.
 *
 * @return true indicates the response queue is full, false otherwise.
 */
static inline bool gpu_queue_full_resp(gpu_queue_handle_t *h)
{
    return h->resp_queue->tail - h->resp_queue->head + 1 == h->capacity;
}

/**
 * Get the number of elements in the request queue.
 *
 * @param h queue handle containing request and response queues.
 *
 * @return number of elements in the queue.
 */
static inline uint32_t gpu_queue_length_req(gpu_queue_handle_t *h)
{
    return (h->req_queue->tail - h->req_queue->head);
}

/**
 * Get the number of elements in the response queue.
 *
 * @param h queue handle containing request and response queues.
 *
 * @return number of elements in the queue.
 */
static inline uint32_t gpu_queue_length_resp(gpu_queue_handle_t *h)
{
    return (h->resp_queue->tail - h->resp_queue->head);
}

/**
 * Enqueue an element into the request queue.
 *
 * @param h queue handle containing request queue to enqueue to.
 * @param req gpu request to enqueue.
 *
 * @return -1 when request queue is full, 0 on success.
 */
static inline int gpu_enqueue_req(gpu_queue_handle_t *h, gpu_req_t req)
{
    gpu_req_t *gpu_req;
    gpu_req_queue_t *gpu_req_q;

    if (gpu_queue_full_req(h)) {
        return -1;
    }

    gpu_req_q = h->req_queue;
    gpu_req = gpu_req_q->buffers + (gpu_req_q->tail % h->capacity);
    sddf_memcpy(gpu_req, &req, sizeof(gpu_req_t));

    gpu_req_q->tail++;

    return 0;
}

/**
 * Enqueue an element into the response queue.
 * This indicates the request has been processed and a response is ready.
 *
 * @param h queue handle containing response queue to enqueue to.
 * @param resp response to enqueue.
 *
 * @return -1 when response queue is full, 0 on success.
 */
static inline int gpu_enqueue_resp(gpu_queue_handle_t *h, gpu_resp_t resp)
{
    gpu_resp_t *gpu_resp;
    gpu_resp_queue_t *gpu_resp_q;
    if (gpu_queue_full_resp(h)) {
        return -1;
    }

    gpu_resp_q = h->resp_queue;
    gpu_resp = gpu_resp_q->buffers + (gpu_resp_q->tail % h->capacity);
    gpu_resp->status = resp.status;
    gpu_resp->id = resp.id;

    gpu_resp_q->tail++;

    return 0;
}

/**
 * Dequeue an element from the request queue.
 *
 * @param h queue handle containing request queue to dequeue from.
 * @param req pointer to store dequeued request.
 *
 * @return -1 when request queue is empty, 0 on success.
 */
static inline int gpu_dequeue_req(gpu_queue_handle_t *h, gpu_req_t *req)
{
    gpu_req_t *gpu_req;
    gpu_req_queue_t *gpu_req_q;
    if (gpu_queue_empty_req(h)) {
        return -1;
    }

    gpu_req_q = h->req_queue;
    gpu_req = gpu_req_q->buffers + (gpu_req_q->head % h->capacity);
    sddf_memcpy(req, gpu_req, sizeof(gpu_req_t));

    gpu_req_q->head++;

    return 0;
}

/**
 * Dequeue an element from a response queue.
 *
 * @param h queue handle containing response queue to dequeue from.
 * @param resp pointer to store dequeued response.
 * @return -1 when response queue is empty, 0 on success.
 */
static inline int gpu_dequeue_resp(gpu_queue_handle_t *h, gpu_resp_t *resp)
{
    gpu_resp_t *gpu_resp;
    gpu_resp_queue_t *gpu_resp_q;
    if (gpu_queue_empty_resp(h)) {
        return -1;
    }

    gpu_resp_q = h->resp_queue;
    gpu_resp = gpu_resp_q->buffers + (gpu_resp_q->head % h->capacity);
    resp->status = gpu_resp->status;
    resp->id = gpu_resp->id;

    gpu_resp_q->head++;

    return 0;
}
