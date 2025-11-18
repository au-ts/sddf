/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <microkit.h>
#include <stdint.h>

/* Describe the configuration space that all PCI device implements.
   Document referenced: https://wiki.osdev.org/PCI */

/* I/O Port */

/* An invalid read of any registers in the configuration space yields this value. */
#define PCI_INVAID_READ 0xffff

#define PCI_HEADER_TYPE_GENERAL 0
#define PCI_HEADER_TYPE_PCI_TO_PCI_BRIDGE 1
#define PCI_HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE 2

#define PCI_CLASS_UNCLASSIFIED 0
#define PCI_CLASS_MASS_STORAGE_CONTROLLER 1
#define PCI_CLASS_NETWORK_CONTROLLER 2
#define PCI_CLASS_DISPLAY_CONTROLLER 3
#define PCI_CLASS_MULTIMEDIA_CONTROLLER 4
#define PCI_CLASS_MEMORY_CONTROLLER 5
#define PCI_CLASS_BRIDGE 6
#define PCI_CLASS_SIMPLE_COMM_CONTROLLER 7
#define PCI_CLASS_BASE_SYS_PERIPHERAL 8
#define PCI_CLASS_INPUT_DEVICE_CONTROLLER 9
#define PCI_CLASS_DOCKING_STATION 10
#define PCI_CLASS_PROCESSOR 11
#define PCI_CLASS_SERIAL_BUS_CONTROLLER 12
#define PCI_CLASS_WIRELESS_CONTROLLER 13
#define PCI_CLASS_INTELLIGENT_CONTROLLER 14
#define PCI_CLASS_SATELLITE_COMM_CONTROLLER 15
#define PCI_CLASS_ENCRYPTION_CONTROLLER 16
#define PCI_CLASS_SIG_PROCESSING_CONTROLLER 17
#define PCI_CLASS_PROCESSING_ACCELERATOR 18
#define PCI_CLASS_NON_ESSENTIAL_INSTRUMENTATIONS 19

#define PCI_CLASS_NETWORK_SUBCLASS_ETHERNET 0

/* Every PCI devices implement these common header fields: */
typedef volatile struct __attribute__((packed)) pci_common_hdr {
    uint16_t vendor_id;      /* Identifies a manufacturer. PCI-SIG allocated. */
    uint16_t device_id;      /* Identifies a particular device. Vendor allocated. */
    uint16_t command;        /* Controls a device's ability to generate and respond to PCI cycles. */
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
