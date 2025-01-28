/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <os/sddf.h>
#include <stdbool.h>
#include <stdint.h>
#include <sddf/resources/common.h>
#include <sddf/resources/device.h>

#define SDDF_NET_MAX_CLIENTS 64

#define SDDF_NET_MAGIC_LEN 5
static char SDDF_NET_MAGIC[SDDF_NET_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x5 };

typedef struct net_connection_resource {
    region_resource_t free_queue;
    region_resource_t active_queue;
    uint16_t num_buffers;
    uint8_t id;
} net_connection_resource_t;

typedef struct net_driver_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t virt_rx;
    net_connection_resource_t virt_tx;
} net_driver_config_t;

typedef struct net_virt_tx_client_config {
    net_connection_resource_t conn;
    device_region_resource_t data;
} net_virt_tx_client_config_t;

typedef struct net_virt_tx_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t driver;
    net_virt_tx_client_config_t clients[SDDF_NET_MAX_CLIENTS];
    uint8_t num_clients;
} net_virt_tx_config_t;

typedef struct net_virt_rx_config_client {
    net_connection_resource_t conn;
    uint8_t mac_addr[6];
} net_virt_rx_config_client_t;

typedef struct net_virt_rx_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t driver;
    device_region_resource_t data;
    // The system designer must allocate a buffer metadata region for internal
    // use by the RX virtualiser. The size of this region must be at least
    // 4*drv_queue_capacity. It must be mapped R-W and zero-initialised.
    region_resource_t buffer_metadata;
    net_virt_rx_config_client_t clients[SDDF_NET_MAX_CLIENTS];
    uint8_t num_clients;
} net_virt_rx_config_t;

typedef struct net_copy_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t virt_rx;
    region_resource_t device_data;

    net_connection_resource_t client;
    region_resource_t client_data;
} net_copy_config_t;

typedef struct net_client_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t rx;
    region_resource_t rx_data;

    net_connection_resource_t tx;
    region_resource_t tx_data;

    uint8_t mac_addr[6];
} net_client_config_t;

static bool net_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_NET_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_NET_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
