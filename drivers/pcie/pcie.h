/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <microkit.h>

// PCI Capability IDs
#define PCI_CAP_ID_PM       0x01    // Power Management
#define PCI_CAP_ID_AGP      0x02    // AGP
#define PCI_CAP_ID_VPD      0x03    // Vital Product Data
#define PCI_CAP_ID_SLOTID   0x04    // Slot Identification
#define PCI_CAP_ID_MSI      0x05    // Message Signaled Interrupts
#define PCI_CAP_ID_CHSWP    0x06    // CompactPCI HotSwap
#define PCI_CAP_ID_PCIX     0x07    // PCI-X
#define PCI_CAP_ID_HT       0x08    // HyperTransport
#define PCI_CAP_ID_VNDR     0x09    // Vendor Specific
#define PCI_CAP_ID_DBG      0x0A    // Debug port
#define PCI_CAP_ID_CCRC     0x0B    // CompactPCI Central Resource Control
#define PCI_CAP_ID_SHPC     0x0C    // PCI Standard Hot-Plug Controller
#define PCI_CAP_ID_SSVID    0x0D    // Bridge subsystem vendor/device ID
#define PCI_CAP_ID_AGP3     0x0E    // AGP Target PCI-PCI bridge
#define PCI_CAP_ID_SECDEV   0x0F    // Secure Device
#define PCI_CAP_ID_EXP      0x10    // PCI Express
#define PCI_CAP_ID_MSIX     0x11    // MSI-X
#define PCI_CAP_ID_SATA     0x12    // SATA Data/Index Conf.
#define PCI_CAP_ID_AF       0x13    // PCI Advanced Features
#define PCI_CAP_ID_EA       0x14    // PCI Enhanced Allocation


typedef struct pcie_driver_config {
    void *ecam_base;
    uint64_t ecam_size;
    uint8_t bus_range;
} pcie_driver_config_t;

// Type 0 headers for endpoints
struct pci_config_space {
    // Device Identification
    uint16_t vendor_id;           // 0x00: Vendor ID
    uint16_t device_id;           // 0x02: Device ID
    uint16_t command;             // 0x04: Command Register
    uint16_t status;              // 0x06: Status Register
    uint8_t revision_id;         // 0x08: Revision ID
    uint8_t prog_if;             // 0x09: Programming Interface
    uint8_t subclass;            // 0x0A: Sub Class Code
    uint8_t class_code;          // 0x0B: Base Class Code
    uint8_t cache_line_size;     // 0x0C: Cache Line Size
    uint8_t latency_timer;       // 0x0D: Latency Timer
    uint8_t header_type;         // 0x0E: Header Type
    uint8_t bist;                // 0x0F: Built-in Self Test

    // Base Address Registers (BARs)
    uint32_t bar[6];              // 0x10-0x27: Base Address Registers

    // Subsystem Information
    uint32_t cardbus_cis_ptr;     // 0x28: CardBus CIS Pointer
    uint16_t subsystem_vendor_id; // 0x2C: Subsystem Vendor ID
    uint16_t subsystem_device_id; // 0x2E: Subsystem Device ID
    uint32_t expansion_rom_addr;  // 0x30: Expansion ROM Base Address

    // Capabilities and Interrupts
    uint8_t cap_ptr;             // 0x34: Capabilities Pointer
    uint8_t reserved1[3];        // 0x35-0x37: Reserved
    uint32_t reserved2;           // 0x38-0x3B: Reserved
    uint8_t interrupt_line;      // 0x3C: Interrupt Line
    uint8_t interrupt_pin;       // 0x3D: Interrupt Pin
    uint8_t min_gnt;             // 0x3E: Min_Gnt
    uint8_t max_lat;             // 0x3F: Max_Lat

    // Capability list
    uint8_t cap_data[192];
};

// =========== ACPI ============

#define BIOS_AREA_START 0xE0000
#define BIOS_AREA_END 0x100000

/**
 * Root System Description Pointer (RSDP)
 * https://wiki.osdev.org/RSDP
 *  */
typedef struct acpi_rsdp {
    char signature[8];  // "RSD PTR "
    uint8_t checksum;   // Checksum of first 20 bytes
    char oem_id[6];
    uint8_t revision;   // 0 for ACPI 1.0, 2 for ACPI 2.0+
    uint32_t rsdt_addr; // 32-bit RSDT address (ACPI 1.0)
    uint32_t length;    // Length (ACPI 2.0+)
    uint64_t xsdt_addr; // 64-bit XSDT address (ACPI 2.0+)
    uint8_t ext_checksum; // Checksum of all fields
    uint8_t reserved[3];
} acpi_rsdp_t;

/**
 * System Description Table Header
 *
 * All SDT share the same header but have different data part.
 * See https://wiki.osdev.org/RSDT for more details.
 *  */
typedef struct acpi_sdt_header {
    char signature[4];
    uint32_t length;
    uint8_t revision;
    uint8_t checksum;
    char oem_id[6];
    char oem_table_id[8];
    uint32_t oem_revision;
    uint32_t creator_id;
    uint32_t creator_revision;
} acpi_sdt_header_t;

/**
 *
 * MCFG Table is structured as:
 *   - ACPI SDT Header
 *   - 8-byte reserved area
 *   - A list of memory mapped configuration base address allocation structures.
 *
 * ECAM Base Address Allocation Structure
 *
 * see PCI Firmware Specification 3.3 Table 4-3 for more details.
 * */
typedef struct mcfg_ecam_alloc {
    uint64_t base_addr;
    uint16_t pci_seg_group;
    uint8_t start_bus;
    uint8_t end_bus;
    uint32_t reserved;
} mcfg_ecam_alloc_t;

// Shared Capability Structure
struct shared_pci_cap {
    uint8_t cap_id;               /* Generic PCI field: PCI_CAP_ID_VNDR */
    uint8_t next_ptr;             /* Generic PCI field: next ptr. */
};

// MSI Message Control Register
struct msi_msg_ctrl {
    uint8_t msi_enable : 1;       /* Enable MSI (RW)*/
    uint8_t mul_msg_cap: 3;       /* Multiple Message Capable: table_size = 2 ** (mul_msg_cap) (RO) */
    uint8_t mul_msg_en: 3;        /* Multiple Message Enable: table_size = 2 ** (mul_msg_en) (RW) */
    uint8_t addr_64 : 1;          /* 64-bit Address Capable (RO) */
    uint8_t per_vec_masking : 1;  /* Per-Vector Masking Capable (RO) */
    uint8_t ext_msg_data_cap : 1; /* Extended Message Data Capable (RO) */
    uint8_t ext_msg_data_en : 1;  /* Extended Message Data Enable (RW) */
    uint8_t reserved : 5;
} __attribute__((packed));

// MSI-X Message Control Register
struct msix_msg_ctrl {
    uint16_t table_size : 11;     /* Real Table Size = table_size + 1 */
    uint8_t reserved : 3;
    uint8_t func_mask : 1;        /* Function Mask: disable all interrupts if set */
    uint8_t msix_enable : 1;      /* MSI-X Enable */
} __attribute__((packed));

// MSI Capability (ID: 0x05)
struct msi_capability {
    uint8_t cap_id;               /* Generic PCI field: PCI_CAP_ID_VNDR */
    uint8_t next_ptr;             /* Generic PCI field: next ptr. */
    uint16_t msg_ctrl;            /* Message Control register */
    uint32_t msg_addr;            /* Message Address */
    uint32_t msg_addr_upper;      /* Message Address - high 32 bits */
    uint16_t msg_data;            /* Message Data */
    uint16_t reserved;
};

// MSI-X Capability (ID 0x11)
struct msix_capability {
    uint8_t cap_id;               /* Generic PCI field: PCI_CAP_ID_VNDR */
    uint8_t next_ptr;             /* Generic PCI field: next ptr. */
    struct msix_msg_ctrl msg_ctrl; /* Message Control register */
    uint32_t table_offset_bir;    /* Table offset and BAR indicator */
    uint32_t pba_offset_bir;      /* Pending bit array offset and BAR */
};

// MSI-X Table Structure
struct msix_table {
    uint32_t msg_addr_low;
    uint32_t msg_addr_hi;
    uint32_t msg_data;
    uint32_t vec_ctrl;
};

#define DEV_MAX_BARS 6
#define ECAM_MAX_REQUESTS 64

typedef enum bar_locatable {
    any_32b, less_1m, any_64b
} bar_locatable_t;

typedef enum irq_type : uint8_t {
    legacy, msi, msix
} irq_type_t;

typedef struct mem_bar {
    uint8_t bar_id;
    uint64_t base_addr;
    bool mem_mapped;
    uint8_t locatable;
    bool prefetchable;
} mem_bar_t;

typedef struct config_request {
    uint8_t bus;
    uint8_t dev;
    uint8_t func;
    uint16_t device_id;
    uint16_t vendor_id;
    mem_bar_t mem_bars[DEV_MAX_BARS];
    irq_type_t irq_type;
} config_request_t;

typedef struct pci_ecam_config {
    char magic[5];
    uint8_t num_requests;
    config_request_t requests[ECAM_MAX_REQUESTS];
} pci_ecam_config_t;
