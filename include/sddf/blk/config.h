/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <sddf/resources/common.h>
#include <sddf/resources/device.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>

#define SDDF_BLK_MAX_CLIENTS (MICROKIT_MAX_CHANNELS - 1)

typedef struct blk_connection_resource {
    region_resource_t storage_info;
    region_resource_t req_queue;
    region_resource_t resp_queue;
    uint16_t num_buffers;
    uint8_t id;
} blk_connection_resource_t;

typedef struct blk_driver_config {
    blk_connection_resource_t virt;
} blk_driver_config_t;

typedef struct blk_virt_config_client {
    blk_connection_resource_t conn;
    device_region_resource_t data;
    uint32_t partition;
} blk_virt_config_client_t;

typedef struct blk_virt_config_driver {
    blk_connection_resource_t conn;
    device_region_resource_t data;
} blk_virt_config_driver_t;

typedef struct blk_virt_config {
    uint64_t num_clients;
    blk_virt_config_driver_t driver;
    blk_virt_config_client_t clients[SDDF_BLK_MAX_CLIENTS];
} blk_virt_config_t;

typedef struct blk_client_config {
    blk_connection_resource_t virt;
    region_resource_t data;
} blk_client_config_t;
