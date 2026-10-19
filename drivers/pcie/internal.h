/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/acpi/handover.h>
#include <sddf/pcie/config.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

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

/* ============ Config space types ============ */

#define PCI_HEADER_TYPE_ENDPOINT 0
#define PCI_HEADER_TYPE_PCI_TO_PCI_BRIDGE 1

#define PCI_COMMAND_IO_SPACE_MASK BIT(0)
#define PCI_COMMAND_MEM_SPACE_MASK BIT(1)

#define PCI_BAR_IO_SPACE_MASK BIT(0)
#define PCI_BAR_PREFETCHABLE_MASK BIT(3)
#define PCI_BAR_ADDR_MASK 0xFFFFFFF0

typedef struct {
    uint16_t vendor_id;      // 0x00: Vendor ID
    uint16_t device_id;      // 0x02: Device ID
    uint16_t command;        // 0x04: Command Register
    uint16_t status;         // 0x06: Status Register
    uint8_t revision_id;     // 0x08: Revision ID
    uint8_t prog_if;         // 0x09: Programming Interface
    uint8_t subclass;        // 0x0A: Sub Class Code
    uint8_t class_code;      // 0x0B: Base Class Code
    uint8_t cache_line_size; // 0x0C: Cache Line Size
    uint8_t latency_timer;   // 0x0D: Latency Timer
    uint8_t header_type;     // 0x0E: Header Type
    uint8_t bist;            // 0x0F: Built-in Self Test
} __attribute__((__packed__)) pci_conf_space_common_hdr_t;

// Type 0 PCI configuration space header for endpoints
#define PCI_TYPE_0_NUM_BARS 6

typedef struct {
    pci_conf_space_common_hdr_t hdr;

    // Base Address Registers (BARs)
    uint32_t bars[PCI_TYPE_0_NUM_BARS]; // 0x10-0x27: Base Address Registers

    // Subsystem Information
    uint32_t cardbus_cis_ptr;     // 0x28: CardBus CIS Pointer
    uint16_t subsystem_vendor_id; // 0x2C: Subsystem Vendor ID
    uint16_t subsystem_device_id; // 0x2E: Subsystem Device ID
    uint32_t expansion_rom_addr;  // 0x30: Expansion ROM Base Address

    // Capabilities and Interrupts
    uint8_t cap_ptr;              // 0x34: Capabilities Pointer
    uint8_t reserved1[3];         // 0x35-0x37: Reserved
    uint32_t reserved2;           // 0x38-0x3B: Reserved
    uint8_t interrupt_line;       // 0x3C: Interrupt Line
    uint8_t interrupt_pin;        // 0x3D: Interrupt Pin
    uint8_t min_gnt;              // 0x3E: Min_Gnt
    uint8_t max_lat;              // 0x3F: Max_Lat

    // Capability list
    uint8_t cap_data[0x1000 - 0x40];
} __attribute__((__packed__)) pci_conf_space_endpoint_t;

_Static_assert(sizeof(pci_conf_space_endpoint_t) == 0x1000, "PCIe config space must be 4 KiB");

// Type 1 PCI configuration space header for switches, bridges, etc.
typedef struct {
    pci_conf_space_common_hdr_t hdr;

    uint32_t bar0;                // 0x10: Base Address Register 0
    uint32_t bar1;                // 0x14: Base Address Register 1

    uint8_t primary_bus_num;      // 0x18: primary bus number
    uint8_t secondary_bus_num;    // 0x19: Secondary bus number
    uint8_t subordinate_bus_num;  // 0x1A: Secondary bus number
    uint8_t secondary_latency_timer; // 0x1B: Secondary bus number

    uint8_t io_base;              // 0x1C: I/O port base address
    uint8_t io_limit;             // 0x1D: I/O port address
    uint16_t secondary_status;    // 0x1E: Secondary Status

    uint16_t mem_base;            // 0x20: Memory Base
    uint16_t mem_limit;           // 0x22: Memory Limit
    uint16_t pre_mem_base;        // 0x24: Prefetchable Memory Base
    uint16_t pre_mem_limit;       // 0x26: Prefetchable Memory Limit
    uint32_t pre_mem_base_upper;  // 0x28: Prefetchable Memory Base Upper Bits
    uint32_t pre_mem_limit_upper; // 0x2C: Prefetchable Memory Limit Upper Bits
    uint16_t io_base_upper;       // 0x30: I/O Base Upper
    uint16_t io_limit_upper;      // 0x32: I/O Limit Upper

    uint8_t cap_ptr;              // 0x34: Capability Pointer
    uint8_t reserved[3];
    uint32_t exp_rom_base;        // 0x38: Expand ROM Base Address
    uint8_t interrupt_line;       // 0x3C: Interrupt Line
    uint8_t interrupt_pin;        // 0x3D: Interrupt Pin
    uint16_t bridge_ctrl;         // 0x3E: Bridge Control

    uint8_t cap_data[0x1000 - 0x40];
} __attribute__((__packed__)) pci_conf_space_bridge_t;

_Static_assert(sizeof(pci_conf_space_bridge_t) == 0x1000, "PCIe config space must be 4 KiB");

/* ============ Internal types and helpers ============ */

/* How many functions of every devices of every buses of every segments the driver can keep track of.
 * We need to keep track of all of them, since the BAR allocator need to consider all functions. */
#define MAX_NUM_PCIE_FUNCTIONS 256

typedef struct {
    /* We need to record this because a 64-bit BAR take up 2 BARs in
     * the config space, thus the `bars` table is sparse */
    bool valid;
    uint64_t paddr;
    uint64_t size_bytes;
    uint8_t prefetchable;
} pcie_bar_info_t;

// #define PCIE_FUNC_INTX_LINE_NONE ((int16_t)-1)
#define PCIE_FUNC_OWNER_NONE ((int8_t)-1)
#define PCIE_FUNC_GSI_NONE 0xFFFFFFFF

typedef struct {
    uint8_t bus, dev, func;
    pci_path_t path;
    host_bridge_t *hb;
    volatile pci_conf_space_endpoint_t *cs;

    uint8_t num_bars;
    pcie_bar_info_t bars[PCI_TYPE_0_NUM_BARS];

    // uint8_t intx_pin;   /* 0 = none */
    // int16_t intx_line;  /* index into intx_lines */
    uint32_t gsi;

    int8_t owner;       /* index into pcie_driver_config_t->clients */
    // uint8_t intx_ch_id; /* owner's channel for INTx */
    bool intx_masked;   /* we set Interrupt Disable, waiting for the owner's ack */
} pcie_function_t;

#define FUNCTION_TABLE_INDEX_NONE ((int64_t)-1)
typedef int64_t pcie_func_table_idx_t;

typedef struct {
    uint32_t gsi;
    microkit_channel ch;    /* our own channel the IRQ handler cap signals */
} intx_line_t;

#define MAX_NUM_INTX_LINES 16

typedef struct {
    bool initialised;
    acpi_handover_t *handover;
    pcie_driver_config_t *config;

    uint64_t vaddr_watermark;

    void *ecams_vaddr[ACPI_MAX_NUM_MCFG_ENTRIES];

    size_t num_funcs;
    pcie_function_t funcs_table[MAX_NUM_PCIE_FUNCTIONS];

    pcie_func_table_idx_t spec_to_func[SDDF_PCIE_MAX_CLIENTS][SDDF_PCIE_MAX_DEVICE_SPECS_PER_CLIENT];

    size_t num_intx_lines;
    intx_line_t intx_lines[MAX_NUM_INTX_LINES];
} pcie_drv_state_t;

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
bool map_ecams(pcie_drv_state_t *driver_state);

/* These functions have no side effects */
bool bus_and_segment_to_ecam_idx(pcie_drv_state_t *driver_state, uint16_t segment, uint8_t bus, size_t *idx);
pci_conf_space_common_hdr_t *pci_geo_addr_to_conf_space(void *ecam, uint8_t bus, uint8_t dev, uint8_t func);

/* ============ Bus management ============ */

/* For each host bridge described by the firmware DSDT/SSDTs, scan it for the devices we care about.
 * Then, for each function of said device, work out their:
 * 1. Global System Interrupt (GSI) number
 * 2. Base Address Registers (BARs) paddr and sizes. (TODO) Assign them if firmware had not assign them.
 * 3. Fill out funcs_table.
 *
 * Can return false if the firmware left things in a buggy state or an unimplemented code path is entered. */
bool host_bridges_scan(pcie_drv_state_t *driver_state);

/* For each PCIe function recorded by `host_bridges_scan`, attempt to match it against a spec in
 * in the clients' specs table given by the metaprogram. Returns false if we can't match a spec
 * to a PCIe function for all specs. */
bool match_specs_to_functions(pcie_drv_state_t *driver_state);

/* For all specs, map all the client requested resources such as BARs and interrupt to the client. */
bool bind_functions_to_clients(pcie_drv_state_t *driver_state);