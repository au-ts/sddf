/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <microkit.h>
#include <stdint.h>

/* Describe the configuration space that all PCI device implements.
   For more information, visit: https://wiki.osdev.org/PCI */

/* I/O Port */

/* An invalid read of any registers in the configuration space yields this value. */
#define PCI_INVAID_READ 0xffff

#define PCI_HEADER_TYPE_GENERAL 0
#define PCI_HEADER_TYPE_PCI_TO_PCI_BRIDGE 1
#define PCI_HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE 2

/* Every PCI devices implement these common header fields: */
typedef volatile struct __attribute__((packed)) pci_common_hdr {
    uint16_t vendor_id;      /* Identifies a manufacturer. PCI-SIG allocated. */
    uint16_t device_id;      /* Identifies a particular device. Vendor allocated. */
    uint16_t command;        /* Controls a device's ability to generate and respond to PCI cycle.s */
    uint16_t status;         /* Records PCI-bus related events. */
    uint8_t rev_id;          /* Identifies revision of a device. Vendor allocated. */
    uint8_t prog_if;         /* Specifies whether device has a register-level programming interface. */
    uint8_t subclass;        /* Identifies sub-function of the class this device is in. */
    uint8_t class_code;      /* Identifies the type of function this device performs. */
    uint8_t cache_line_size; /* Specifies system cache line size in 32-bit units. */
    uint8_t latency_timer;   /* Specifies latency timer in units of PCI bus clocks. */
    uint8_t header_type;     /* Identifies the layout of the rest of the header. */
    uint8_t bist;            /* Records status of Built-in Self Test. */
} pci_common_hdr_t;

/* A general device implement this header: */
#define PCI_GEN_DEV_NUM_BARS 6

typedef volatile struct __attribute__((packed)) pci_gen_dev_hdr {
    pci_common_hdr_t common_hdr;
    uint32_t base_address_registers[PCI_GEN_DEV_NUM_BARS];
    uint32_t cardbus_cis_ptr;
    uint16_t subsystem_ven_id;
    uint16_t subsystem_id;
    uint32_t exp_rom_base_addr;
    uint8_t cap_ptr;
    uint8_t reserved[7];
    uint8_t irq_line;
    uint8_t irq_pin;
    uint8_t min_grant;
    uint8_t max_latency;
} pci_gen_dev_hdr_t;

_Static_assert(sizeof(pci_gen_dev_hdr_t) == 256, "pci_gen_dev_hdr_t must be 256 bytes large.");

// /* Argument and return types for the various functions below. */
// typedef struct pci_dev_identifier {
//     uint16_t vendor_id;
//     uint16_t device_id;
//     uint8_t revision_id;
//     uint8_t class_code;
//     uint8_t subclass;
//     uint8_t padding;
// } pci_dev_id_t;

// typedef struct pci_dev_addr {
//     uint8_t 
// } pci_dev_bus_addr_t

// /* Given the PCI device's details, find its position on the PCI bus. Returns true if found. */

// bool pci_discover_device();

// /* Given 2 capabilities to the PCI config data I/O Ports, and a general PCI device's bus location. Reads
//    that device's configuration header. */
// //bool 