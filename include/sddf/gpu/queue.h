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

#define GPU_MAX_SCANOUTS 16
#define GPU_MAX_RESOURCES 1024 /* restrict resource ids to 0..GPU_MAX_RESOURCES, strictly this #define isn't necessary but simplifies implementation */

/* Request code for gpu */
typedef enum gpu_req_code {
    /* 2d commands */
    GPU_REQ_RESOURCE_CREATE_2D, /* create resource from other side */
    GPU_REQ_RESOURCE_UNREF, /* destroy resource from other side */
    GPU_REQ_RESOURCE_ATTACH_BACKING, /* assign shared contiguous memory to resource */
    GPU_REQ_RESOURCE_DETACH_BACKING, /* unassign the shared memory used in resource */
    GPU_REQ_SET_SCANOUT, /* set the scanout of a resource */
    GPU_REQ_TRANSFER_TO_2D, /* notifies other side that data in resource has been updated */
    GPU_REQ_RESOURCE_FLUSH, /* flushes resource from other side to scanout */
} gpu_req_code_t;

/* Response status for gpu */
typedef enum gpu_resp_status {
    GPU_RESP_OK, /* success response */
    GPU_RESP_ERR_UNSPEC, /* for misc errors, e.g. attaching backing to a resource that already has backing */
    GPU_RESP_ERR_OUT_OF_MEMORY, /* out of memory to assign to resource */
    GPU_RESP_ERR_INVALID_SCANOUT_ID, /* scanout id does not exist */
    GPU_RESP_ERR_INVALID_RESOURCE_ID, /* resource id does not exist */
    GPU_RESP_ERR_INVALID_BOUNDS, /* transfer bounds outside of resource/scanout */
} gpu_resp_status_t;

/* Request struct contained in request queue */
typedef struct gpu_req {
    gpu_req_code_t code; /* request code */
    uint32_t id; /* stores request id */
    uint32_t resource_id; /* resource id to be assigned to resource */
    union {
        gpu_req_resource_create_2d_t resource_create_2d;
        gpu_req_resource_unref_t resource_unref;
        gpu_req_resource_attach_backing_t resource_attach_backing;
        gpu_req_resource_detach_backing_t resource_detach_backing;
        gpu_req_set_scanout_t set_scanout;
        gpu_req_transfer_to_2d_t transfer_to_2d;
        gpu_req_resource_flush_t resource_flush;
    };
} gpu_req_t;

/* Response struct contained in response queue */
typedef struct gpu_resp {
    gpu_resp_status_t status; /* response status */
    uint32_t id; /* stores corresponding request id */
} gpu_resp_t;

/* Configuration struct contained in config queue */
typedef struct gpu_config {
    gpu_scanout_t scanouts[GPU_MAX_SCANOUTS]; /* per-scanout info, its index maps to scanout_id */
    uint32_t num_scanouts; /* number of scanouts available */
} gpu_config_t;

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

/* Circular buffer containing configuration updates */
typedef struct gpu_config_queue {
    uint32_t tail;
    uint32_t head;
    gpu_config_t buffers[];
} gpu_config_queue_t;

/* A queue handle for queueing/dequeueing request and responses */
typedef struct gpu_queue_handle {
    gpu_req_queue_t *req_queue;
    gpu_resp_queue_t *resp_queue;
    gpu_config_queue_t *config_queue;
    uint32_t capacity; /* number of entries in the req and resp queue */
    uint32_t config_capacity; /* number of entries in the config queue */
} gpu_queue_handle_t;

/**
 * Initialise the shared queues.
 *
 * @param h queue handle to use.
 * @param request pointer to request queue in shared memory.
 * @param response pointer to response queue in shared memory.
 * @param config pointer to config queue in shared memory.
 * @param capacity number of entries in the req and resp queues.
 * @param config_capacity number of entries in the config queue.
 */
static inline void gpu_queue_init(gpu_queue_handle_t *h,
                                  gpu_req_queue_t *request,
                                  gpu_resp_queue_t *response,
                                  gpu_config_queue_t *config,
                                  uint32_t capacity,
                                  uint32_t config_capacity)
{
    h->req_queue = request;
    h->resp_queue = response;
    h->config_queue = config;
    h->capacity = capacity;
    h->config_capacity = config_capacity;
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
 * Check if the config queue is empty.
 *
 * @param h queue handle containing config queue.
 *
 * @return true indicates the config queue is empty, false otherwise.
 */
static inline bool gpu_queue_empty_config(gpu_queue_handle_t *h)
{
    return h->config_queue->tail - h->config_queue->head == 0;
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
 * Check if the config queue is full.
 *
 * @param h queue handle containing config queue.
 *
 * @return true indicates the config queue is full, false otherwise.
 */
static inline bool gpu_queue_full_config(gpu_queue_handle_t *h)
{
    return h->config_queue->tail - h->config_queue->head + 1 == h->config_capacity;
}

/**
 * Get the number of elements in the request queue.
 *
 * @param h queue handle containing request and response queues.
 *
 * @return number of elements in the queue.
 */
static inline int gpu_queue_length_req(gpu_queue_handle_t *h)
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
static inline int gpu_queue_length_resp(gpu_queue_handle_t *h)
{
    return (h->resp_queue->tail - h->resp_queue->head);
}

/**
 * Get the number of elements in the config queue.
 *
 * @param h queue handle containing config queue.
 *
 * @return number of elements in the queue.
 */
static inline int gpu_queue_length_config(gpu_queue_handle_t *h)
{
    return (h->config_queue->tail - h->config_queue->head);
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
 * Enqueue an element into the config queue.
 *
 * @param h queue handle containing config queue to enqueue to.
 * @param config config to enqueue.
 *
 * @return -1 when config queue is full, 0 on success.
 */
static inline int gpu_enqueue_config(gpu_queue_handle_t *h, gpu_config_t config)
{
    gpu_config_t *gpu_config;
    gpu_config_queue_t *gpu_config_q;
    if (gpu_queue_full_config(h)) {
        return -1;
    }

    gpu_config_q = h->config_queue;
    gpu_config = gpu_config_q->buffers + (gpu_config_q->tail % h->config_capacity);
    for (int i = 0; i < GPU_MAX_SCANOUTS; i++) {
        gpu_scanout_t *so_local = config.scanouts + i;
        gpu_scanout_t *so_shared = gpu_config->scanouts + i;
        gpu_rect_t *so_rect_local = &so_local->rect;
        gpu_rect_t *so_rect_shared = &so_shared->rect;
        so_rect_shared->x = so_rect_local->x;
        so_rect_shared->y = so_rect_local->y;
        so_rect_shared->width = so_rect_local->width;
        so_rect_shared->height = so_rect_local->height;
        so_shared->enabled = so_local->enabled;
    }
    gpu_config->num_scanouts = config.num_scanouts;

    gpu_config_q->tail++;

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

/**
 * Dequeue an element from the config queue.
 *
 * @param h queue handle containing config queue to dequeue from.
 * @param config pointer to store config.
 *
 * @return -1 when config queue is empty, 0 on success.
 */
static inline int gpu_dequeue_config(gpu_queue_handle_t *h, gpu_config_t *config)
{
    gpu_config_t *gpu_config;
    gpu_config_queue_t *gpu_config_q;
    if (gpu_queue_empty_config(h)) {
        return -1;
    }

    gpu_config_q = h->config_queue;
    gpu_config = gpu_config_q->buffers + (gpu_config_q->head % h->config_capacity);
    for (int i = 0; i < GPU_MAX_SCANOUTS; i++) {
        gpu_scanout_t *so_local = config->scanouts + i;
        gpu_scanout_t *so_shared = gpu_config->scanouts + i;
        gpu_rect_t *so_rect_local = &so_local->rect;
        gpu_rect_t *so_rect_shared = &so_shared->rect;
        so_rect_local->x = so_rect_shared->x;
        so_rect_local->y = so_rect_shared->y;
        so_rect_local->width = so_rect_shared->width;
        so_rect_local->height = so_rect_shared->height;
        so_local->enabled = so_shared->enabled;
    }
    config->num_scanouts = gpu_config->num_scanouts;

    gpu_config_q->head++;

    return 0;
}
