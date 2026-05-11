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
    /**
     * The Rx virtualiser uses the buffer_metadata region for storing reference
     * counts of Rx DMA buffers as they are passed to clients. This is
     * particularly important in the case of broadcast, as buffers can only be
     * safely returned to the driver for re-use once they have been freed by all
     * clients.
     *
     * The region must be mapped R-W, zero-initialised and large enough to store
     * a count for each buffer ( >= sizeof(uint8_t) * drv_queue_capacity bytes).
     */
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
    region_resource_t tx_data;
    /**
     * The mac address field is ignored in the case of the virtualiser port.
     */
    mac_addr_t mac_addr;
    uint64_t acl;
} net_vswitch_port_config_t;

typedef struct net_vswitch_config {
    char magic[SDDF_NET_MAGIC_LEN];

    /**
     * Ports encode the vswitch's connection with both the virtualisers and its
     * clients. The ports array is ordered as follows:
     *
     * ports[0 : num_ports] - client ports
     * ports[num_ports].rx - Tx virtualiser connection
     * ports[num_ports].tx - Rx virtualiser connection
     *
     * The rx connection is mapped to the tx virtualiser and vice versa, as it
     * allows the vswitch to handle the virtualiser port the same way as a
     * client port.
     */
    net_vswitch_port_config_t ports[SDDF_NET_MAX_CLIENTS];
    uint8_t num_ports;

    /**
     * The vswitch uses the buffer_metadata region for storing reference counts
     * of each of its clients Tx buffers, as well as the Rx DMA buffers. Since a
     * client may transmit a buffer to more than endpoint, the reference count
     * ensures that the vswitch only returns a buffer once it has been freed by
     * all its recipients.
     *
     * The region must be mapped R-W, zero-initialised and large enough to store
     * a count for each buffer:
     *
     * (ports[0].tx.capacity + ... + ports[num_ports].tx.capacity) * sizeof(uin8_t) bytes
     */
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
