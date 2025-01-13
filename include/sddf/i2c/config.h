/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <microkit.h>
#include <sddf/resources/common.h>
#include <sddf/resources/device.h>
#include <sddf/i2c/queue.h>

#define SDDF_I2C_MAX_CLIENTS (MICROKIT_MAX_CHANNELS - 1)

typedef struct i2c_connection_resource {
    region_resource_t data;
    region_resource_t req_queue;
    region_resource_t resp_queue;
    uint16_t num_buffers;
    uint8_t id;
} i2c_connection_resource_t;

typedef struct i2c_driver_config {
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
    uint64_t num_clients;
    i2c_virt_driver_config_t driver;
    i2c_virt_client_config_t clients[SDDF_I2C_MAX_CLIENTS];
} i2c_virt_config_t;

typedef struct i2c_client_config {
    i2c_connection_resource_t virt;
} i2c_client_config_t;
