/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <microkit.h>
#include <stdbool.h>
#include <stdint.h>
#include <sddf/resources/common.h>
#include <sddf/resources/device.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>

#define SDDF_BLK_MAX_CLIENTS 64

#define SDDF_BLK_MAGIC_LEN 5
static char SDDF_BLK_MAGIC[SDDF_BLK_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x2 };

typedef struct blk_connection_resource {
    region_resource_t storage_info;
    region_resource_t req_queue;
    region_resource_t resp_queue;
    uint16_t num_buffers;
    uint8_t id;
} blk_connection_resource_t;

typedef struct blk_driver_config {
    char magic[SDDF_BLK_MAGIC_LEN];
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
    char magic[SDDF_BLK_MAGIC_LEN];
    uint64_t num_clients;
    blk_virt_config_driver_t driver;
    blk_virt_config_client_t clients[SDDF_BLK_MAX_CLIENTS];
} blk_virt_config_t;

typedef struct blk_client_config {
    char magic[SDDF_BLK_MAGIC_LEN];
    blk_connection_resource_t virt;
    region_resource_t data;
} blk_client_config_t;

static bool blk_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_BLK_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_BLK_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
