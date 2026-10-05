/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <sddf/util/tlsf/tlsf.h>

#define PAGE_SIZE_4K BIT(seL4_PageBits)

#define ACPI_HEAP_SIZE 0x400000
#define MAX_PADDR_MAPPED 1024

#define ACPI_DIRECT_MAP_BASE BIT(30)

#define RSDP_PADDR (ACPI_DIRECT_MAP_BASE - PAGE_SIZE_4K)

typedef struct {
    void *vaddr;
    uint64_t paddr;
    size_t size_bytes;
    uint16_t segment;
    uint8_t start_bus;
    uint8_t end_bus;
} lib_sddf_uacpi_ecam_desc_t;

typedef struct {
    void *config_space_vaddr; // in one of the ECAM
} pci_device_uacpi_handle_t;

#define MAX_NUM_ECAM 4
#define MAX_ECAM_VADDR ACPI_DIRECT_MAP_BASE

typedef struct {
    size_t irq_cslot;
    size_t ntfn_cslot;
    uacpi_interrupt_handler uacpi_callback;
    uacpi_handle uacpi_ctx;
} irq_handle_t;

typedef struct {
    char acpi_heap_buf[ACPI_HEAP_SIZE];
    /* Annoyingly, seL4 give us the RSDP blob rather than the paddr, so we need
    * to copy it into a dummy "paddr" and serve it to uACPI from a buffer. */
    char rsdp_buf[PAGE_SIZE_4K];

    tlsf_t acpi_heap;

    shadow_cnode_t *post_capdl_shadow_cnode;
    seL4_CPtr vspace_cptr;
    seL4_CPtr x86_ioport_ctrl_cptr;

    /* We map physical memory with vaddr as ACPI_DIRECT_MAP_BASE + requested paddr
    * so that we don't have to unmap it and do cap clean ups, since we will tear
    * everything down by the end anyways.

    * @billn improve by reserving this range in the linker? */
    uint64_t paddr_mapped[MAX_PADDR_MAPPED];
    size_t num_p_mapped;

    lib_sddf_uacpi_ecam_desc_t ecams[MAX_NUM_ECAM];
    size_t num_ecams;
    uint64_t next_avail_ecam_vaddr;

    irq_handle_t *sci_handle;
} lib_sddf_uacpi_state_t;