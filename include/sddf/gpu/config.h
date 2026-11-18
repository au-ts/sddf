/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <stdbool.h>
#include <stdint.h>
#include <sddf/resources/common.h>
#include <sddf/resources/device.h>
#include <sddf/gpu/queue.h>
#include <sddf/gpu/events.h>

/*
 * Configuration structures for the GPU device class. These are populated at
 * build time by the Acacia metaprogram (see acacia_sddf/gpu.py) and patched
 * into the corresponding ELF sections.
 */

#define SDDF_GPU_MAX_CLIENTS 64
/* Upper bound on the capacity of any GPU request/response queue */
#define SDDF_GPU_MAX_QUEUE_CAPACITY 1024

#define SDDF_GPU_MAGIC_LEN 5
static char SDDF_GPU_MAGIC[SDDF_GPU_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x7 };

typedef struct gpu_connection_resource {
    /* Shared events region (e.g. display info changed) */
    region_resource_t events;
    region_resource_t req_queue;
    region_resource_t resp_queue;
    /* Capacity of both request and response queues */
    uint16_t num_buffers;
    /* Channel id of the other end of the connection */
    uint8_t id;
} gpu_connection_resource_t;

typedef struct gpu_driver_config {
    char magic[SDDF_GPU_MAGIC_LEN + 1];
    gpu_connection_resource_t virt;
    /* Region shared with the virtualiser, used to return GET_DISPLAY_INFO data */
    region_resource_t data;
} gpu_driver_config_t;

typedef struct gpu_virt_config_client {
    gpu_connection_resource_t conn;
    /* Client's data region. The I/O address is used to translate client
     * memory offsets into addresses the device can access. */
    device_region_resource_t data;
} gpu_virt_config_client_t;

typedef struct gpu_virt_config_driver {
    gpu_connection_resource_t conn;
    device_region_resource_t data;
} gpu_virt_config_driver_t;

typedef struct gpu_virt_config {
    char magic[SDDF_GPU_MAGIC_LEN + 1];
    uint64_t num_clients;
    gpu_virt_config_driver_t driver;
    gpu_virt_config_client_t clients[SDDF_GPU_MAX_CLIENTS];
} gpu_virt_config_t;

typedef struct gpu_client_config {
    char magic[SDDF_GPU_MAGIC_LEN + 1];
    gpu_connection_resource_t virt;
    /* Memory that resources are backed by and display info is written to */
    region_resource_t data;
} gpu_client_config_t;

static inline bool gpu_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_GPU_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_GPU_MAGIC[i]) {
            return false;
        }
    }

    return true;
}

/* Initialise a queue handle from a connection resource */
static inline void gpu_queue_init_from_conn(gpu_queue_handle_t *h, gpu_connection_resource_t *conn)
{
    gpu_queue_init(h, (gpu_req_queue_t *)conn->req_queue.vaddr, (gpu_resp_queue_t *)conn->resp_queue.vaddr,
                   conn->num_buffers);
}
