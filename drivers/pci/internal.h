/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include "pci.h"
#include <sddf/util/util.h>

/* ============ Debugging ============ */

#define CONFIG_DEBUG_DRIVER

#if defined(CONFIG_DEBUG_DRIVER)
#define DEBUG_DRIVER(fmt, ...) \
    sddf_dprintf("PCI DRIVER %s:%d|INFO: " fmt, __func__, __LINE__, ##__VA_ARGS__)
#else
#define DEBUG_DRIVER(fmt, ...) do {} while (0)
#endif

#define DEBUG_DRIVER_ERR(fmt, ...) \
    sddf_dprintf("PCI DRIVER %s:%d|ERROR: " fmt, __func__, __LINE__, ##__VA_ARGS__)

const char *pci_class_and_subclass_to_string(uint8_t class, uint8_t subclass);
void dump_acpi_info(acpi_handover_t *post_acpi_handover);

/* ============ Types and helpers ============ */

typedef struct {
    bool initialised;
    acpi_handover_t *handover;

    uint64_t vaddr_watermark;

    void *ecams_vaddr[ACPI_MAX_NUM_MCFG_ENTRIES];
} pci_drv_state_t;

#define CPTR_POST_ACPI_CNODE  (microkit_cspace_root_slot_to_cptr(1))
#define CPTR_SELF_VSPACE    (microkit_cspace_root_slot_to_cptr(2))

/* In the PCI B:D.F address, device is 5 bits, function is 3 bits. Then each device have a 4K
 * configuration space. */
#define PCI_DEV_BITS 5
#define PCI_FUNC_BITS 3
#define PCIE_SIZE_BYTES_PER_BUS (BIT(PCI_DEV_BITS) * BIT(PCI_FUNC_BITS) * 0x1000)

#define NO_VENDOR 0xffff

#define ACPI_DRIVER_CH 0

/* ============ ECAMs management ============ */

/* Map all ECAMs described by the firmware MCFG. */
bool map_ecams(pci_drv_state_t *driver_state);

/* These functions have no side effects */
bool bus_and_segment_to_ecam_idx(pci_drv_state_t *driver_state, uint16_t segment, uint8_t bus, size_t *idx);
pci_conf_space_common_hdr_t *pci_geo_addr_to_conf_space(void *ecam, uint8_t bus, uint8_t dev, uint8_t func);

/* ============ Bus management ============ */

/* For each host bridge described by the firmware DSDT/SSDTs, scan it for the devices we care about.
 * Then, for each said device, work out their:
 * 1. Global System Interrupt (GSI) number
 * 2. Base Address Registers (BARs) paddr and sizes. Assign them if firmware had not assign them. */
bool host_bridges_scan(pci_drv_state_t *driver_state);