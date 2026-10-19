/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

#define SDDF_PCIE_MAGIC_LEN 5
static char SDDF_PCIE_MAGIC[SDDF_PCIE_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x67 }; // @billn check number

/* Maximum number of device specs per client. A client normally claims a single PCIe device,
 * and 8 specs covers every function of one multi-function device. Increase this if a driver
 * ever needs to claim several devices. */
#define SDDF_PCIE_MAX_DEVICE_SPECS_PER_CLIENT 8

#define SDDF_PCIE_MAX_CLIENTS 64

#define SDDF_PCIE_DEVICE_INSTANCE_ANY 0xFFFF
#define SDDF_PCIE_DEVICE_SPEC_VENDOR_ID_ANY 0xFFFF
#define SDDF_PCIE_DEVICE_SPEC_DEVICE_ID_ANY 0xFFFF
#define SDDF_PCIE_DEVICE_SPEC_FUNCTION_ID_ANY 0xFF
#define SDDF_PCIE_DEVICE_SPEC_CLASS_CODE_ANY 0xFFFFFFFF

#define SDDF_PCIE_DEVICE_MAX_NUM_BARS 6

typedef struct {
    /* We need to record this because a 64-bit BAR take up 2 BARs in
     * the config space, thus the `bars` table is sparse */
    uint8_t entry_valid;

    uint64_t map_addr;
    uint64_t min_size;
    uint64_t max_size;
} pcie_mem_bar_spec_t;

typedef struct {
    uint16_t instance;       /* nth match in scan order, or SDDF_PCIE_DEVICE_INSTANCE_ANY */
    uint16_t vendor, device;
    uint8_t function;
    uint32_t class_code;     /* 0x00:class:subclass:prog-if */
    uint8_t bus_master;      /* can DMA? If yes and x86 then the IOMMU needs to be set up,
                              * Microkit >= 2.3.0 turns on the Intel VT-d IOMMU by default. */

    pcie_mem_bar_spec_t bars[SDDF_PCIE_DEVICE_MAX_NUM_BARS];

    uint8_t map_intx;
    uint32_t ch_id;
} pcie_device_spec_t;

typedef struct {
    uint8_t id;
    uint64_t cspace_slot;
    uint64_t vspace_slot;
    uint8_t vspace_is_x86_ept;

    uint8_t num_specs;
    pcie_device_spec_t specs[SDDF_PCIE_MAX_DEVICE_SPECS_PER_CLIENT];
} pcie_connection_resource_t;

typedef struct {
    char magic[SDDF_PCIE_MAGIC_LEN];

    pcie_connection_resource_t clients[SDDF_PCIE_MAX_CLIENTS];
    uint64_t num_clients;
} pcie_driver_config_t;

static inline bool pcie_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_PCIE_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_PCIE_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
