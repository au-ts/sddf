/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/common.h>
#include <sddf/resources/device.h>
#include <sddf/i2c/queue.h>

#define SDDF_I2C_MAX_CLIENTS 64

#define SDDF_I2C_MAGIC_LEN 5
static char SDDF_I2C_MAGIC[SDDF_I2C_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x4 };

// Generic connection between any two places in the I2C system
typedef struct i2c_connection_resource {
    region_resource_t req_queue;
    region_resource_t resp_queue;
    uint16_t num_req_buffers;
    uint16_t num_resp_buffers;
    uint8_t id;
} i2c_connection_resource_t;

typedef struct i2c_driver_config {
    char magic[SDDF_I2C_MAGIC_LEN + 1];
    i2c_connection_resource_t virt;
} i2c_driver_config_t;

// Description of a client for the i2c virt. Part of i2c_virt_config only.
typedef struct i2c_virt_client_config {
    i2c_connection_resource_t conn;
    size_t data_size;
    uintptr_t driver_data_vaddr;
    uintptr_t client_data_vaddr;
} i2c_virt_client_config_t;

// General virt configuration
typedef struct i2c_virt_config {
    char magic[SDDF_I2C_MAGIC_LEN + 1];
    uint64_t num_clients;
    i2c_connection_resource_t driver;
    region_resource_t intermediary_mr;
    i2c_virt_client_config_t clients[SDDF_I2C_MAX_CLIENTS];
} i2c_virt_config_t;

// Per-client configuration
typedef struct i2c_client_config {
    char magic[SDDF_I2C_MAGIC_LEN + 1];
    i2c_connection_resource_t virt;
    region_resource_t data;
} i2c_client_config_t;

static inline bool i2c_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_I2C_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_I2C_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
