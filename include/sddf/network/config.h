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

typedef struct net_virt_tx_client_config {
    net_connection_resource_t conn;
    device_region_resource_t data;
} net_virt_tx_client_config_t;

// TODO: this could be commonalized with net_virt_tx_vswitch_config, but who cares for now
typedef struct net_virt_tx_vswitch_config {
    net_connection_resource_t conn;
    device_region_resource_t data[SDDF_NET_MAX_CLIENTS];
    uint8_t data_id[SDDF_NET_MAX_CLIENTS];
} net_virt_tx_vswitch_config_t;

typedef struct net_virt_tx_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t driver;
    net_virt_tx_client_config_t clients[SDDF_NET_MAX_CLIENTS];
    net_virt_tx_vswitch_config_t vswitch;
    uint8_t num_clients;
} net_virt_tx_config_t;

typedef struct net_virt_rx_config_client {
    net_connection_resource_t conn;
    uint8_t mac_addr[MAC802_BYTES];
} net_virt_rx_config_client_t;

typedef struct net_virt_rx_config {
    char magic[SDDF_NET_MAGIC_LEN];
    net_connection_resource_t driver;
    device_region_resource_t data;
    // The system designer must allocate a buffer metadata region for internal
    // use by the RX virtualiser. The size of this region must be at least
    // sizeof(int*)*drv_queue_capacity. It must be mapped R-W and zero-initialised.
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

    uint8_t mac_addr[MAC802_BYTES];
} net_client_config_t;

// TODO: remove
#define TEMP_MAX_MACS_PER_CLIENT 3

typedef struct net_vswitch_port_config {
    net_connection_resource_t rx;
    region_resource_t rx_data; // TODO: check that we need that
    net_connection_resource_t tx;
    region_resource_t tx_data;
    /* unused for the device */
    mac_addr_t mac_addrs[TEMP_MAX_MACS_PER_CLIENT]; // TODO: fix the dimension
    uint8_t id;
} net_vswitch_port_config_t;

typedef struct net_vswitch_config {
    char magic[SDDF_NET_MAGIC_LEN];

    // TODO: we need the data buffers mapped since we are forwarding packets and need to access them, unless we specify a way of proxying them without introspection
    // Ports
    /* Rx/Tx swapped for the virtualizer */
    net_vswitch_port_config_t ports[SDDF_NET_MAX_CLIENTS];
    uint8_t num_ports;

    // Reference counting buffers; interfaced as array[NUM_CLIENTS + 1][drv_queue_capacity]
    // The system designer must allocate a buffer big enough to contain reference counters for buffers.
    // The size of this region must be at least (NUM_CLIENTS + 1) * drv_queue_capacity * sizeof(int*).
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
