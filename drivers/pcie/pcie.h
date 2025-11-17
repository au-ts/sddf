/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <microkit.h>

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

struct acpi_rsdp {
    char signature[8];  // "RSD PTR "
    uint8_t checksum;   // Checksum of first 20 bytes
    char oem_id[6];
    uint8_t revision;   // 0 for ACPI 1.0, 2 for ACPI 2.0+
    uint32_t rsdt_addr; // 32-bit RSDT address (ACPI 1.0)
    uint32_t length;    // Length (ACPI 2.0+)
    uint64_t xsdt_addr; // 64-bit XSDT address (ACPI 2.0+)
};
