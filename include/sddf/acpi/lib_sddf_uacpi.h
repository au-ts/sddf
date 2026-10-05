/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>

#include <sddf/util/shadow_cnode.h>

/* Root System Descriptor Pointer */
typedef struct lib_sddf_uacpi_rsdp {
    char         signature[8];
    uint8_t      checksum;
    char         oem_id[6];
    uint8_t      revision;
    uint32_t     rsdt_address;
    uint32_t     length;
    uint64_t     xsdt_address;
    uint8_t      extended_checksum;
    char         reserved[3];
} __attribute__((packed)) lib_sddf_uacpi_rsdp_t;

typedef struct {
    lib_sddf_uacpi_rsdp_t *rsdp_blob;
    shadow_cnode_t *post_capdl_shadow_cnode;
    seL4_CPtr vspace_cptr;
} sddf_uacpi_init_args_t;

/* Given all the UTs granted to the post initialiser component from the capDL
 * initialiser and other control caps in a CNode, initialise uACPI and the
 * port layer lib_sddf_uacpi. lib_sddf_uacpi retain exclusive control
 * of this CNode and all of its caps until sddf_uacpi_teardown is called.
 *
 * This may fail under the following scenarios:
 * 1. Out of heap memory for uACPI. Fix: increase ACPI_HEAP_SIZE
 * 2. Insufficient device UTs to map memory at certain physical addresses required by
 *    uACPI. Fix: avoid creating frames in device memory inside the capDL
 *    initialiser. This will cause the entire parent UT to be unavailable
 *    to the post initialiser component. Allocate this memory with the PCI
 *    driver instead.
 * 3. Insufficient normal UTs to make paging objects for mapping memory.
 * 4. Out of bookkeeping memory in uacpi_kernel_map(). This can happen when
 *    uACPI tries to map too much physical memory. Fix: increase MAX_PADDR_MAPPED.
 * 5. Out of CSlot, can happen when mapping too much memory.
 *    Fix: increase post capDL CNode size bits.
 * 6. x86: overlapping I/O Port mappings between the capDL initialiser and
 *    uACPI, lib_sddf_uacpi will reserve the entire I/O Port range
 *    while it is active. Fix: see #2.
 * */
bool sddf_uacpi_init(sddf_uacpi_init_args_t *init_args);

/* Deinitialise all data structures relating to uACPI and revoke all caps
 * that where granted to it, resetting the CNode and its caps to the state
 * that was originally given to sddf_uacpi_init(). */
bool sddf_uacpi_teardown(void);