/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>

#include <sddf/util/cspace.h>

/* Root System Descriptor Pointer */
typedef struct acpi_rsdp {
    char         signature[8];
    uint8_t      checksum;
    char         oem_id[6];
    uint8_t      revision;
    uint32_t     rsdt_address;
    uint32_t     length;
    uint64_t     xsdt_address;
    uint8_t      extended_checksum;
    char         reserved[3];
} __attribute__((packed)) acpi_rsdp_t;

typedef struct {
    acpi_rsdp_t *rsdp_blob;
    cnode_specs_t *ut_cnode;
} sddf_uacpi_init_args_t;

bool sddf_uacpi_init(sddf_uacpi_init_args_t *init_args);
