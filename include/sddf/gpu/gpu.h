/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

/* Defines a rectangle with position x, y and size with width, length.
 * The coordinates 0,0 is top left, larger x moves right, larger y moves down.
*/
typedef struct gpu_rect {
    uint32_t x;
    uint32_t y;
    uint32_t width;
    uint32_t height;
} gpu_rect_t;

/* Scanout info */
typedef struct gpu_scanout {
    gpu_rect_t rect; /* (x, y) indicates the preferred position of scanout, (width, length) is the scanout's dimensions */
    bool enabled;
} gpu_scanout_t;

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

typedef struct gpu_req_resource_create_2d {
    uint32_t resource_id; /* resource id to be assigned to resource */
    uint32_t width; /* width of resource */
    uint32_t height; /* height of resource */
    gpu_formats_t format; /* format of resource */
} gpu_req_resource_create_2d_t;

typedef struct gpu_req_resource_unref {
    uint32_t resource_id;
} gpu_req_resource_unref_t;

typedef struct gpu_req_resource_attach_backing {
    uint32_t resource_id;
    uintptr_t io_or_offset; /* offset within memory region or io address of the memory backing */
    uint32_t data_size; /* size in bytes of the memory backing */
} gpu_req_resource_attach_backing_t;

typedef struct gpu_req_resource_detach_backing {
    uint32_t resource_id;
} gpu_req_resource_detach_backing_t;

typedef struct gpu_req_set_scanout {
    uint32_t scanout_id;
    uint32_t resource_id;
    gpu_rect_t rect; /* rectangle within real/emulated scanout that a resource is scanned out to */
} gpu_req_set_scanout_t;

typedef struct gpu_req_transfer_to_2d {
    uint32_t resource_id;
    gpu_rect_t rect; /* rectangle in the resource to transfer framebuffer data to other side */
    uint32_t offset; /* offset into the resource, from which framebuffer data begins */
} gpu_req_transfer_to_2d_t;

typedef struct gpu_req_resource_flush {
    uint32_t resource_id;
    gpu_rect_t rect; /* rectangle in the resource to flush to scanout */
} gpu_req_resource_flush_t;
