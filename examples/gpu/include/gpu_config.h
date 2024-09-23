/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stddef.h>
#include <sddf/util/string.h>
#include <sddf/gpu/queue.h>
#include <sddf/gpu/events.h>

#define GPU_NUM_CLIENTS                     1

#define GPU_NAME_CLI0                       "client"

#define GPU_QUEUE_CAPACITY_CLI0             1024
#define GPU_QUEUE_CAPACITY_DRV              1024

#define GPU_DATA_REGION_SIZE_CLI0           0x200000
#define GPU_DATA_REGION_SIZE_DRV            0x1000
#define GPU_QUEUE_REGION_SIZE_CLI0          0x200000
#define GPU_QUEUE_REGION_SIZE_DRV           0x200000

/*
 * These are sizes of the regions that hold virtIO information, such as the virtq (metadata)
 * and the memory that descriptors would point to (data).
 */
#define GPU_VIRTIO_METADATA_REGION_SIZE     0x200000
#define GPU_VIRTIO_DATA_REGION_SIZE         0x200000

static inline gpu_events_t *gpu_virt_cli_events_region(gpu_events_t *events, unsigned int id)
{
    switch (id) {
    case 0:
        return events;
    default:
        return NULL;
    }
}

static inline gpu_req_queue_t *gpu_virt_cli_req_queue(gpu_req_queue_t *req, unsigned int id)
{
    switch (id) {
    case 0:
        return req;
    default:
        return NULL;
    }
}

static inline gpu_resp_queue_t *gpu_virt_cli_resp_queue(gpu_resp_queue_t *resp, unsigned int id)
{
    switch (id) {
    case 0:
        return resp;
    default:
        return NULL;
    }
}

static inline uintptr_t gpu_virt_cli_data_region(uintptr_t data, unsigned int id)
{
    switch (id) {
    case 0:
        return data;
    default:
        return 0;
    }
}

static inline uint64_t gpu_virt_cli_data_region_size(unsigned int id)
{
    switch (id) {
    case 0:
        return GPU_DATA_REGION_SIZE_CLI0;
    default:
        return 0;
    }
}

static inline uint32_t gpu_virt_cli_queue_capacity(unsigned int id)
{
    switch (id) {
    case 0:
        return GPU_QUEUE_CAPACITY_CLI0;
    default:
        return 0;
    }
}

static inline uint32_t gpu_cli_queue_capacity(char *pd_name)
{
    if (!sddf_strcmp(pd_name, GPU_NAME_CLI0)) {
        return GPU_QUEUE_CAPACITY_CLI0;
    } else {
        return 0;
    }
}
