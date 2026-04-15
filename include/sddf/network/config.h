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
#include <sddf/network/mac802.h>

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

typedef struct net_virt_tx_data_region {
    device_region_resource_t data;
    uint32_t num_buffers;
} net_virt_tx_data_region_t;

typedef struct net_virt_tx_client_config {
    net_connection_resource_t conn;
    net_virt_tx_data_region_t regions[SDDF_NET_MAX_CLIENTS];
    uint8_t num_regions;
} net_virt_tx_client_config_t;

typedef struct net_virt_tx_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t driver;
    net_virt_tx_client_config_t clients[SDDF_NET_MAX_CLIENTS];
    uint8_t num_clients;
} net_virt_tx_config_t;

typedef struct net_virt_rx_client_config {
    net_connection_resource_t conn;
    mac_addr_t mac_addrs[SDDF_NET_MAX_CLIENTS];
    uint8_t num_macs;
} net_virt_rx_client_config_t;

typedef struct net_virt_rx_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t driver;
    device_region_resource_t data;
    // The Rx virtualiser uses a reference count system to keep track of buffer ownership.
    // This is particularly important when a buffer is broadcast to multiple clients,
    // as the buffer can only be safely returned to the driver for re-use once it has been freed by all clients.
    // These reference counts are stored in the buffer_metadata region,
    // thus the region must be large enough to store a count for each Rx DMA buffer in the system
    // (i.e. >= sizeof(uint8_t) * drv_queue_capacity bytes). It must also be mapped R-W and zero-initialised.
    region_resource_t buffer_metadata;
    net_virt_rx_client_config_t clients[SDDF_NET_MAX_CLIENTS];
    uint8_t num_clients;
} net_virt_rx_config_t;

typedef struct net_copy_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t rx;
    region_resource_t rx_data[SDDF_NET_MAX_CLIENTS];

    net_connection_resource_t client;
    region_resource_t client_data;
} net_copy_config_t;

typedef struct net_client_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t rx;
    region_resource_t rx_data;

    net_connection_resource_t tx;
    region_resource_t tx_data;

    mac_addr_t mac_addr;
} net_client_config_t;

typedef struct net_vswitch_port_config {
    net_connection_resource_t rx;
    net_connection_resource_t tx;
    device_region_resource_t tx_data;
    /* unused for the virts */
    mac_addr_t mac_addr;
    uint64_t acl;
} net_vswitch_port_config_t;

typedef struct net_vswitch_config {
    char magic[SDDF_NET_MAGIC_LEN];

    /* The first num_ports entries in this array are the vswitch's clients.
     * The next port after the last client, index num_ports contains the vswitch's connection with the virtualisers.
     * However, the rx field is the connection with Tx virtualiser, and the tx field is the connection with the Rx virtualiser.
     * This allows the vswitch to treat the virtualiser the same way as it's other clients. */
    net_vswitch_port_config_t ports[SDDF_NET_MAX_CLIENTS];
    uint8_t num_ports;

    // Reference counting buffers; The system designer must allocate a buffer big enough to contain reference counters for buffers.
    // The size of this region must be equal to at least num_ports * number_of_buffers_per_port * sizeof(uint8_t).
    // It must be mapped R-W and zero-initialised.
    region_resource_t buffer_metadata;
} net_vswitch_config_t;

static inline bool net_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_NET_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_NET_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
