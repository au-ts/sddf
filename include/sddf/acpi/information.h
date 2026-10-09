/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <sddf/util/shadow_cnode.h>

/* What the short-lived ACPI driver will handover to the long-lived PCIe driver */

#define ACPI_HANDOVER_MAGIC 0x5DDFAC61

#define ACPI_MAX_NUM_HOST_BRIDGES 1
#define ACPI_MAX_NUM_CRS_PER_HOST_BRIDGE 8
#define ACPI_MAX_NUM_PRT_PER_HOST_BRIDGE 512
#define ACPI_MAX_NUM_ISA_DEVICES 4
#define ACPI_MAX_NUM_MADT_ISO_ENTRIES 16
#define ACPI_MAX_NUM_MCFG_ENTRIES 4

/* ACPI Spec Release 6.5, Section 6.1.5 _HID (Hardware ID) */
#define ACPI_HID_LEN 9

/* "Current Resource Setting" */
typedef enum {
    CRS_KIND_MEMORY = 1,
    CRS_KIND_IO,
    CRS_KIND_BUS,
} crs_entry_kind_t;

typedef struct {
    uint8_t kind;
    uint64_t base;
    uint64_t end_inclusive;
} crs_entry_t;

/* "PCI Routing Table" */
#define ACPI_MAX_PCI_PATH_DEPTH 4
typedef struct {
    uint8_t depth; /* 0 = host bridge's own _PRT */
    uint8_t devfn[ACPI_MAX_PCI_PATH_DEPTH];  /* (dev << 3) | fn per hop, host bridge first */
} pci_path_t;

typedef struct {
    pci_path_t path;
    uint8_t slot;
    uint8_t pin; /* 0 = INTA */
    uint8_t level_triggered;
    uint8_t active_low;
    uint32_t gsi;
} prt_entry_t;

/* PCI Host Bridge description */
typedef struct {
    uint64_t segment;
    uint64_t start_bus;
    crs_entry_t crs_entries[ACPI_MAX_NUM_CRS_PER_HOST_BRIDGE];
    size_t num_crs_entry;
    prt_entry_t prt_entries[ACPI_MAX_NUM_PRT_PER_HOST_BRIDGE];
    size_t num_prt_entry;
} host_bridge_t;

/* ISA (non-PCI) device description */
typedef struct {
    char acpi_hid[ACPI_HID_LEN];
    uint8_t instance;
    crs_entry_t crs;
    uint8_t has_irq;
    uint8_t level_triggered;
    uint8_t active_low;
    uint32_t isa_irq; /* PCIe driver must resolve to GSI using MADT ISO entries */
} isa_dev_desc_t;

/* "Multiple APIC Description Table" (MADT) entries */
typedef struct {
    uint8_t bus;
    uint8_t source;
    uint32_t gsi;
    uint8_t level_triggered;
    uint8_t active_low;
} madt_iso_entry_t;

/* "High Precision Event Timer" details */
typedef struct {
    uint64_t paddr;
    /* "The minimum clock ticks can be set without lost
     * interrupts while the counter is programmed to operate in
     * periodic mode". We don't use periodic mode in our HPET
     * driver so this is moot but useful for the future. */
    uint16_t min_clk_tick;
} hpet_entry_t;

/* PCI MCFG */
typedef struct {
    uint64_t paddr;
    uint16_t segment;
    uint8_t start_bus;
    uint8_t end_bus;
} mcfg_entry_t;

typedef struct {
    uint32_t magic;

    /* Untypeds and control caps details */
    shadow_cnode_t post_acpi_shadow_cnode;

    /* PCI information */
    host_bridge_t host_bridges[ACPI_MAX_NUM_HOST_BRIDGES];
    size_t num_host_bridges;

    /* Entries from firmware-provided MCFG table for mapping PCI segment and start
     * bus to ECAM paddr. */
    mcfg_entry_t mcfg_entries[ACPI_MAX_NUM_MCFG_ENTRIES];
    size_t num_mcfg_entries;

    /* Information about ISA devices that the metaprgram requested for */
    isa_dev_desc_t isa_devices[ACPI_MAX_NUM_ISA_DEVICES];
    size_t num_isa_devices;

    /* Interrupt Source Override and I/O APIC entries from firmware-provided MADT
     * for mapping GSI -> I/O APIC chip and pin. */
    madt_iso_entry_t madt_iso_entries[ACPI_MAX_NUM_MADT_ISO_ENTRIES];
    size_t num_madt_iso_entries;
    uint32_t madt_ioapic_gsi_bases[CONFIG_MAX_NUM_IOAPIC];
    size_t num_madt_ioapics;

    /* From HPET table */
    hpet_entry_t hpet;
    uint8_t hpet_available;

    /* From "Fixed ACPI Description Table" (FADT) */
    uint8_t system_supports_msi;
} acpi_handover_t;