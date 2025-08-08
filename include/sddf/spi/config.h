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

#define SDDF_SPI_MAX_CLIENTS (64)
#define SPI_MAX_CS_LINES SDDF_SPI_MAX_CLIENTS

#define SDDF_SPI_MAGIC_LEN 5
static char SDDF_SPI_MAGIC[SDDF_SPI_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x9 };

// zig: DeviceConfig
typedef struct spi_device_config {
    bool cpha;
    bool cpol;
    uint64_t freq_div;
} spi_device_config_t;

// zig: Client.Connection
typedef struct spi_client_connection_resource {
    region_resource_t cmd_queue;
    region_resource_t resp_queue;
    uint8_t id;
    uint8_t queue_capacity_bits;
} spi_client_connection_resource_t;

// zig: Client
typedef struct spi_client_config {
    char magic[SDDF_SPI_MAGIC_LEN];
    spi_client_connection_resource_t virt;
    region_resource_t data;
} spi_client_config_t;

// zig: Driver.Connection
typedef struct spi_driver_connection_resource {
    region_resource_t cmd_queue;
    region_resource_t resp_queue;
    region_resource_t cmd_cs_queue;
    region_resource_t resp_cs_queue;
    uint8_t id;
    uint8_t queue_capacity_bits;
} spi_driver_connection_resource_t;

// zig: Driver
typedef struct spi_driver_config {
    char magic[SDDF_SPI_MAGIC_LEN];
    spi_driver_connection_resource_t virt;
    region_resource_t data[SPI_MAX_CS_LINES];
    spi_device_config_t dev_config[SPI_MAX_CS_LINES];
} spi_driver_config_t;

// zig: Virt.Client
typedef struct spi_virt_config_client {
    spi_client_connection_resource_t conn;
    uint64_t data_size;
    uint8_t cs;
} spi_virt_config_client_t;

// zig: Virt
typedef struct spi_virt_config {
    char magic[SDDF_SPI_MAGIC_LEN];
    uint8_t num_clients;
    spi_virt_config_client_t clients[SDDF_SPI_MAX_CLIENTS];
    spi_driver_connection_resource_t driver;
} spi_virt_config_t;

static bool spi_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_SPI_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_SPI_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
