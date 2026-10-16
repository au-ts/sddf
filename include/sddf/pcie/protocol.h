/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

/* Shared functionality/definitions between the PCIe driver and its clients */

enum {
    SDDF_PCIE_CLAIM_DEVICE,
    SDDF_PCIE_READ_CS_8,
    SDDF_PCIE_READ_CS_16,
    SDDF_PCIE_READ_CS_32,
    SDDF_PCIE_GET_MEM_BAR,
    SDDF_PCIE_MAP_MEM_BAR,
    SDDF_PCIE_MAP_INTX,
    SDDF_PCIE_ACK_INTX,
};

#define SDDF_PCIE_CLAIM_DEVICE_NUM_WORDS 1
#define SDDF_PCIE_READ_CS_NUM_WORDS 2
#define SDDF_PCIE_GET_MEM_BAR_NUM_WORDS 2
#define SDDF_PCIE_MAP_MEM_BAR_NUM_WORDS 5
#define SDDF_PCIE_MAP_INTX_NUM_WORDS 2
#define SDDF_PCIE_ACK_INTX_NUM_WORDS 1

typedef enum {
    SDDF_PCIE_STATUS_OK = 0,
    SDDF_PCIE_STATUS_TRUNCATED,
    SDDF_PCIE_STATUS_INVALID_ARGUMENT,
    SDDF_PCIE_STATUS_INVALID_HANDLE,
    SDDF_PCIE_STATUS_ALREADY_CLAIMED,
    SDDF_PCIE_STATUS_NOT_FOUND,
    SDDF_PCIE_STATUS_FORBIDDEN,
    SDDF_PCIE_STATUS_MAPPING_FAILED,
} sddf_pcie_status_t;

typedef enum {
    SDDF_PCIE_MEM_CACHE_DISABLED = 0,
    SDDF_PCIE_MEM_CACHE_ENABLED = 1,
} sddf_pcie_mem_attr_t;

typedef uint64_t sddf_pcie_handle_t;