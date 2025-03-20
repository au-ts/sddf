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

typedef struct i2c_connection_resource {
    region_resource_t data;
    region_resource_t req_queue;
    region_resource_t resp_queue;
    uint16_t num_buffers;
    uint8_t id;
} i2c_connection_resource_t;

typedef struct i2c_driver_config {
    char magic[SDDF_I2C_MAGIC_LEN];
    i2c_connection_resource_t virt;
} i2c_driver_config_t;

typedef struct i2c_virt_client_config {
    i2c_connection_resource_t conn;
    uint64_t driver_data_offset;
} i2c_virt_client_config_t;

typedef struct i2c_virt_driver_config {
    i2c_connection_resource_t conn;
} i2c_virt_driver_config_t;

typedef struct i2c_virt_config {
    char magic[SDDF_I2C_MAGIC_LEN];
    uint64_t num_clients;
    i2c_virt_driver_config_t driver;
    i2c_virt_client_config_t clients[SDDF_I2C_MAX_CLIENTS];
} i2c_virt_config_t;

typedef struct i2c_client_config {
    char magic[SDDF_I2C_MAGIC_LEN];
    i2c_connection_resource_t virt;
} i2c_client_config_t;

static bool i2c_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_I2C_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_I2C_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
