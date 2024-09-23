/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

/* Restrict resource ids to 1..GPU_MAX_RESOURCES inclusive */
#define GPU_MAX_RESOURCES 1024
/* Reserved resource id for disabling scanout used during set scanout request */
#define GPU_DISABLE_SCANOUT_RESOURCE_ID 0
/* Bytes per pixel in 2D resources */
#define GPU_BPP_2D 4
#define GPU_MAX_SCANOUTS 16

/* Defines a rectangle with position x, y and size with width, length.
 * The coordinates 0,0 is top left, larger x moves right, larger y moves down.
*/
typedef struct gpu_rect {
    uint32_t x;
    uint32_t y;
    uint32_t width;
    uint32_t height;
} gpu_rect_t;

/* Format associated with each resource */
typedef enum gpu_formats {
    GPU_FORMAT_B8G8R8A8_UNORM,
    GPU_FORMAT_B8G8R8X8_UNORM,
    GPU_FORMAT_A8R8G8B8_UNORM,
    GPU_FORMAT_X8R8G8B8_UNORM,
    GPU_FORMAT_R8G8B8A8_UNORM,
    GPU_FORMAT_X8B8G8R8_UNORM,
    GPU_FORMAT_A8B8G8R8_UNORM,
    GPU_FORMAT_R8G8B8X8_UNORM,
} gpu_formats_t;

typedef struct gpu_scanout {
    /* (x, y) indicates the preferred position of scanout, (width, length) is the scanout's dimensions */
    gpu_rect_t rect;
    bool enabled;
} gpu_scanout_t;

typedef struct gpu_req_get_display_info {
    /* Offset within data memory region */
    uint64_t mem_offset;
} gpu_req_get_display_info_t;

typedef struct gpu_resp_get_display_info {
    /* Per-scanout info, its index maps to scanout_id */
    gpu_scanout_t scanouts[GPU_MAX_SCANOUTS];
    /* Number of scanouts available */
    uint32_t num_scanouts;
} gpu_resp_get_display_info_t;

typedef struct gpu_req_resource_create_2d_blob {
    /* Assign resource with id */
    uint32_t resource_id;
    /* Offset within data memory region */
    uint64_t mem_offset;
    /* Size in bytes of the resource memory */
    uint32_t mem_size;
} gpu_req_resource_create_2d_blob_t;

typedef struct gpu_req_set_scanout_blob {
    uint32_t resource_id;
    uint32_t scanout_id;
    /* Width of resource */
    uint32_t width;
    /* Height of resource */
    uint32_t height;
    /* Format of resource */
    gpu_formats_t format;
    /* Bytes from one row of pixels to the next in resource */
    uint32_t stride;
    /* Offset into resource memory where data in specified shape and format begins */
    uint32_t offset;
    /* The rectangle portion of the blob resource being displayed */
    gpu_rect_t rect;
} gpu_req_set_scanout_blob_t;

typedef struct gpu_req_resource_create_2d {
    /* Assign resource with id */
    uint32_t resource_id;
    /* Width of resource */
    uint32_t width;
    /* Height of resource */
    uint32_t height;
    /* Format of resource */
    gpu_formats_t format;
} gpu_req_resource_create_2d_t;

typedef struct gpu_req_resource_attach_backing {
    uint32_t resource_id;
    /* Offset within data memory region */
    uint64_t mem_offset;
    /* Size in bytes of the memory backing */
    uint32_t mem_size;
} gpu_req_resource_attach_backing_t;

typedef struct gpu_req_resource_detach_backing {
    uint32_t resource_id;
} gpu_req_resource_detach_backing_t;

typedef struct gpu_req_set_scanout {
    uint32_t resource_id;
    uint32_t scanout_id;
    /* Rectangle within resource for data to be scanned out from */
    gpu_rect_t rect;
} gpu_req_set_scanout_t;

typedef struct gpu_req_transfer_to_2d {
    uint32_t resource_id;
    /* Rectangle in destination resource memory where data is transferred to */
    gpu_rect_t rect;
    /* Offset into resource's attached memory backing, from which data is transferred from */
    uint64_t mem_offset;
} gpu_req_transfer_to_2d_t;

typedef struct gpu_req_resource_flush {
    uint32_t resource_id;
    /* Rectangle in the resource to flush to scanout */
    gpu_rect_t rect;
} gpu_req_resource_flush_t;

typedef struct gpu_req_resource_unref {
    uint32_t resource_id;
} gpu_req_resource_unref_t;
