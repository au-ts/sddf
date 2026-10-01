/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>

#include <sddf/util/shadow_cnode.h>

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
    shadow_cnode_t *post_capdl_shadow_cnode;
    seL4_CPtr vspace_cptr;
    seL4_CPtr x86_ioport_ctrl_cptr;
} sddf_uacpi_init_args_t;

bool sddf_uacpi_init(sddf_uacpi_init_args_t *init_args);
