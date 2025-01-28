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

#define SDDF_SERIAL_MAX_CLIENTS 64
#define SDDF_SERIAL_BEGIN_STR_MAX_LEN 128

#define SDDF_SERIAL_MAGIC_LEN 5
static char SDDF_SERIAL_MAGIC[SDDF_SERIAL_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x3 };

typedef struct serial_connection_resource {
    region_resource_t queue;
    region_resource_t data;
    uint8_t id;
} serial_connection_resource_t;

typedef struct serial_driver_config {
    char magic[SDDF_SERIAL_MAGIC_LEN];
    serial_connection_resource_t rx;
    serial_connection_resource_t tx;
    uint64_t default_baud;
    bool rx_enabled;
} serial_driver_config_t;

typedef struct serial_virt_rx_config {
    char magic[SDDF_SERIAL_MAGIC_LEN];
    serial_connection_resource_t driver;
    serial_connection_resource_t clients[SDDF_SERIAL_MAX_CLIENTS];
    uint8_t num_clients;
    char switch_char;
    char terminate_num_char;
} serial_virt_rx_config_t;

typedef struct serial_virt_tx_client_config {
    serial_connection_resource_t conn;
    char name[SDDF_NAME_LENGTH];
} serial_virt_tx_client_config_t;

typedef struct serial_virt_tx_config {
    char magic[SDDF_SERIAL_MAGIC_LEN];
    serial_connection_resource_t driver;
    serial_virt_tx_client_config_t clients[SDDF_SERIAL_MAX_CLIENTS];
    uint8_t num_clients;
    char begin_str[SDDF_SERIAL_BEGIN_STR_MAX_LEN];
    uint8_t begin_str_len;
    bool enable_colour;
    bool enable_rx;
} serial_virt_tx_config_t;

typedef struct serial_client_config {
    char magic[SDDF_SERIAL_MAGIC_LEN];
    serial_connection_resource_t rx;
    serial_connection_resource_t tx;
} serial_client_config_t;

static bool serial_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_SERIAL_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_SERIAL_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
