/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include "pci.h"

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <sel4/sel4_arch/mapping.h>

pci_resources_t *pci_resources = (pci_resources_t *)0x60000000;
cnode_specs_t *cnode_specs;
uint32_t kernel_objects_ut_idx = 2;
pci_bridge_node_t pci_bridge_nodes[10];
uint32_t num_pci_bridge_nodes = 0;

#define CPTR_CNODE_PCI_RESOURCES        (microkit_cspace_root_slot_to_cptr(1))
#define CPTR_VSPACE_ETHERNET_DRIVER     (microkit_cspace_root_slot_to_cptr(2))
#define CPTR_CSPACE_ETHERNET_DRIVER     (microkit_cspace_root_slot_to_cptr(3))

bool acpi_ready = false;

// regions[1..] are used for MSI-X BARs
uint8_t avail_region_idx = 1;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".ecam_configs"))) pci_ecam_config_t pci_ecam_config;

/**
 * Look for the capability of a device by ID
 * */
static struct shared_pci_cap *find_pci_cap_by_id(struct pci_header_type0 *config_space, uint8_t cap_id)
{
    struct shared_pci_cap *cap = (struct shared_pci_cap *)((uintptr_t)config_space + config_space->cap_ptr);
    while (cap != (struct shared_pci_cap *)config_space) {
        if (cap->cap_id == cap_id) {
            return cap;
        }
        cap = (struct shared_pci_cap *)((uintptr_t)config_space + cap->next_ptr);
    }
    return NULL;
}

uint64_t alloc_bar_from_resource_windows(uint32_t bar_request)
{
    /* uint8_t space_indicator = bar_request & 0x1; */
    /* uint8_t bar_width = bar_request & 0x3; */
    /* uint8_t prefetchable = bar_request & 0x1; */
    /* uint32_t bar_size = (~(bar_request) | 0xF) + 1; */

    /* sddf_dprintf("    Space Indicator: %s\n", space_indicator == 1 ? "I/O" : "Memory"); */
    /* sddf_dprintf("    Prefetchable: %s\n", prefetchable ? "true" : "false"); */
    /* sddf_dprintf("    Size: 0x%x\n", bar_size); */
    /* sddf_dprintf("    Width: "); */

    /* enum device_resource_type expected_resource_type; */

    /* switch (bar_width) { */
    /*     case 0: { */
    /*         sddf_dprintf("32-bit BAR\n"); */
    /*         expected_resource_type = DWORD_MEMORY; */
    /*         break; */
    /*     } */
    /*     case 2: { */
    /*         sddf_dprintf("64-bit BAR\n"); */
    /*         expected_resource_type = QWORD_MEMORY; */
    /*         break; */
    /*     } */
    /*     default: { */
    /*         sddf_dprintf("Reserved\n"); */
    /*     } */
    /* } */

    /* for (int i = 0; i < pci_resources->num_bridges; i++) { */
    /*     uint8_t num_res = pci_resources->bridges[i].num_dev_resources; */
    /*     for (int j = 0; j < num_res; j++) { */
    /*         device_resource_t *dev_res = (device_resource_t *)&pci_resources->bridges[i].dev_resources[j]; */
    /*         sddf_dprintf("resource type: %u, min_addr: 0x%lx, max_addr: 0x%lx, type_flags: 0x%x\n", dev_res->type, dev_res->min_addr, dev_res->max_addr, dev_res->flags); */

    /*         if (dev_res->type == expected_resource_type && dev_res->max_addr - dev_res->min_addr >= bar_size) { */
    /*             uint64_t allocated_paddr = dev_res->min_addr; */
    /*             sddf_dprintf("allocated paddr: 0x%lx\n", allocated_paddr); */
    /*             dev_res->min_addr += bar_size; */
    /*             return allocated_paddr; */
    /*         } */
    /*     } */
    /* } */

    return 0;
}

void map_pci_bar(struct pci_header_type0 *pci_header, uint8_t bar_id, uintptr_t target_vaddr)
{
    volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + (bar_id * 0x04));

    // Read pre-allocated physical address
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id + 1, mem_bar[1]);
    bool memory_64bit = (*mem_bar) & 0x4;
    uint64_t prealloc_paddr = *mem_bar;
    if (memory_64bit) {
        prealloc_paddr += ((uint64_t)mem_bar[1] << 32);
    }
    sddf_dprintf("BAR %u - pre-allocated addr: 0x%lx\n", bar_id, prealloc_paddr);

    // Write 1s to read BAR request from device and allocate from resource windows
    *mem_bar = 0xFFFFFFFF;
    uint64_t realloc_paddr = alloc_bar_from_resource_windows(*mem_bar);
    if (realloc_paddr == 0) {
        sddf_dprintf("[Error] failed to allocate requested BAR from resource windows\n");
        return;
    }

    *mem_bar = realloc_paddr & 0xFFFFFFFF;
    if (memory_64bit) {
        *(mem_bar + 1) = realloc_paddr >> 32;
    }
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);

    seL4_Error error;
    uintptr_t cur_paddr = realloc_paddr;
    uintptr_t end_paddr = realloc_paddr + 0x4000;
    uintptr_t cur_vaddr = target_vaddr;
    while (cur_paddr < end_paddr) {
        error = retype_and_map_frame(cnode_specs, cur_paddr, cur_vaddr, CPTR_VSPACE_ETHERNET_DRIVER, seL4_X86_4K, seL4_ReadWrite);
        if (error != seL4_NoError) {
            sddf_dprintf("Error: failed to retype or map a frame.\n");
            return;
        }
        cur_paddr += (1 << seL4_PageBits);
        cur_vaddr += (1 << seL4_PageBits);
    }
}

void configure_irqs(struct pci_header_type0 *pci_header, config_request_t config_request)
{
    bool ioapic_enabled = true;
    for (int i = 0; i < config_request.num_irqs; i++) {
        if (config_request.irqs[i].kind != irq_ioapic) {
            ioapic_enabled = false;
        }

        if (!ioapic_enabled && config_request.irqs[i].kind == irq_ioapic) {
            sddf_dprintf("error: I/O APIC can not be enabled with MSI/MSI-X\n");
            return;
        }
    }

    // Enable/Disable I/O APIC interrupts
    if (ioapic_enabled) {
        pci_header->command &= (~BIT(10));
        return;
    } else {
        pci_header->command |= BIT(10);
    }

    for (int i = 0; i < config_request.num_irqs; i++) {
        switch (config_request.irqs[i].kind) {
            case irq_ioapic: {
                // TODO: figure out how to reconfigure interrupt vectors
                break;
            };
            case irq_msi: {
                // TODO: configure MSI interrupts
                break;
            };
            case irq_msix: {
                break;
            };
            default: {
                sddf_dprintf("error: device does not support MSI-X\n");
            };
        }

    }
}

uint8_t get_pci_bridge_idx_by_bus(uint8_t pci_bus)
{
    for (int i = 0; i < pci_resources->num_bridges; i++) {
        uint8_t num_res = pci_resources->bridges[i].num_dev_resources;
        sddf_dprintf("num_res: %u\n", num_res);
        for (int j = 0; j < num_res; j++) {
            device_resource_t *dev_res = (device_resource_t *)&pci_resources->bridges[i].dev_resources[j];
            /* sddf_dprintf("resource type: %u, min_addr: 0x%lx, max_addr: 0x%lx\n", dev_res->type, dev_res->min_addr, dev_res->max_addr); */

            if (dev_res->type == ACPI_RES_TYPE_BUS) {
                if (pci_bus >= dev_res->min_addr && pci_bus < dev_res->max_addr) {
                    sddf_dprintf("Found the bridge %u[0x%02lx-0x%02lx] containing bus 0x%02x\n", i, dev_res->min_addr, dev_res->max_addr, pci_bus);
                    return i;
                }

            }
        }
    }

    // TODO: if it's not found
    return 0;
}

void configure_msi(struct pci_header_type0 *pci_header, uint8_t vector)
{
    struct msix_capability *msix_cap = (struct msix_capability *)find_pci_cap_by_id(pci_header, PCI_CAP_ID_MSIX);

    if (msix_cap) {
        // Bits 2-0 refer to BAR ID
        uint8_t bar_id = msix_cap->table_offset_bir & 0x5;
        pci_bar_t msix_bar;
        msix_bar.bar_id = bar_id;
        /* msix_bar.base_addr = device_resources.regions[avail_region_idx].io_addr; */
        msix_bar.ioport = false;

        map_pci_bar(pci_header, bar_id, 0x4000000);

        // Enable MSI-X
        struct msix_msg_ctrl *msg_ctrl = &msix_cap->msg_ctrl;
        msg_ctrl->msix_enable = 1;
        sddf_dprintf("Table Size: 0x%x\n", msg_ctrl->table_size + 1);
        sddf_dprintf("Function Mask: 0x%x\n", msg_ctrl->func_mask);
        sddf_dprintf("MSI-X Enable: 0x%x\n", msg_ctrl->msix_enable);

        struct msix_table *msix_table = (struct msix_table *)device_resources.regions[avail_region_idx].region.vaddr;
        msix_table->msg_addr_low = 0xFEEu << 20;
        msix_table->msg_data = 0x4030 + vector;
        msix_table->vec_ctrl = 0x0;
        sddf_dprintf("Vector 0 Message Addr Low: 0x%x\n", msix_table->msg_addr_low);
        sddf_dprintf("Vector 0 Message Addr Hi: 0x%x\n", msix_table->msg_addr_hi);
        sddf_dprintf("Vector 0 Message Data: 0x%x\n", msix_table->msg_data);
        sddf_dprintf("Vector 0 Vector Control: 0x%x\n", msix_table->vec_ctrl);

        uint32_t *msix_pba = (uint32_t *)( + 0x800);
        sddf_dprintf("PBA: 0x%x\n", msix_pba[0]);

    }
}

pci_bridge_t *find_pci_bridge(uintptr_t header_addr, uintptr_t ecam_base)
{
    uintptr_t header_offset = header_addr - ecam_base;
    uint32_t dev_slot = header_offset >> 15;
    uint32_t func_slot = header_offset & 0xFFFF;
    uintptr_t target_bridge_adr = (dev_slot << 16) + func_slot;

    if (header_addr == 0x0) {
        target_bridge_adr = 0x0;
    }
    sddf_dprintf("Target PCI bridge addr: 0x%lx\n", header_offset);
    uint32_t num_bridges = pci_resources->num_bridges;
    for (int i = 0; i < num_bridges; i++) {
        pci_bridge_t *pci_bridge = &pci_resources->bridges[i];
        if (target_bridge_adr == pci_bridge->adr) {
            sddf_dprintf("pci_bridge addr: 0x%lx\n", pci_bridge->adr);
            return pci_bridge;
        }
    }

    return NULL;
}

void bind_irq(pci_bridge_t *pci_bridge, struct pci_header_type0 *pci_header, uint8_t pci_bus, uint8_t pci_dev, uint8_t pci_func, uint8_t irq_num)
{
    uint8_t base_irq_cap = 138;

    uint8_t num_prt_entries = pci_bridge->num_prt_entries;
    sddf_dprintf("num_prt_entries: %u\n", num_prt_entries);
    uint8_t gsi_number = 0;
    for (int j = 0; j < num_prt_entries; j++) {
        pci_prt_t *pci_prt = (pci_prt_t *)&pci_bridge->prt_entries[j];
        sddf_dprintf("addr: 0x%X, pin: %u, gsi: %u\n", pci_prt->address, pci_prt->pin, pci_prt->gsi);
        uint32_t dev_num = (pci_prt->address >> 16) & 0x1F;
        uint32_t func_num = pci_prt->address & 0xFFFF;
        if (func_num != 0xFFFF) {
            sddf_dprintf("func numebr: 0x%X, pci_prt->address: 0x%X, &: 0x%X\n", func_num, pci_prt->address, pci_prt->address & 0xFFFF);
            sddf_dprintf("Error: PRT rule (address: 0x%X, pin: %u, gsi: %u) does not apply to the current implementation\n", pci_prt->address, pci_prt->pin, pci_prt->gsi);
            return;
        }

        if (dev_num == pci_dev) {
            gsi_number = pci_prt->gsi;
            sddf_dprintf("Found the GSI numebr %u for the device\n", gsi_number);
            break;
        }
    }

    if (gsi_number == 0) {
        sddf_dprintf("Error: failed to find the PRT rule for PCI device at %02x:%02x.%x\n", pci_bus, pci_dev, pci_func);
        return;
    }

    sddf_dprintf("Try creating an IRQ handler capability: ");
    seL4_Error error = seL4_IRQControl_GetIOAPIC(CPTR_CNODE_PCI_RESOURCES + 1, CPTR_CSPACE_ETHERNET_DRIVER, base_irq_cap + irq_num, 58, 0, gsi_number, 1, 0, 1);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to create an IO/APIC IRQ handler - %d\n", error);
    } else {
        sddf_dprintf("Success!\n");
    }

    sddf_dprintf("Try minting a notification capability: ");
    error = seL4_CNode_Mint(CPTR_CNODE_PCI_RESOURCES, 250, 58, CPTR_CSPACE_ETHERNET_DRIVER, 1, 58, seL4_ReadWrite, 1 << irq_num);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to mint a notification - %d\n", error);
    } else {
        sddf_dprintf("Success!\n");
    }

    seL4_CPtr handler_cap = CPTR_CSPACE_ETHERNET_DRIVER + base_irq_cap + irq_num;
    seL4_CPtr ntf_cap = CPTR_CNODE_PCI_RESOURCES + 250;

    seL4_Word ret = seL4_DebugCapIdentify(handler_cap);
    sddf_dprintf("ret: %lu\n", ret);
    sddf_dprintf("Try bind the handler to notification: ");
    error = seL4_IRQHandler_SetNotification(handler_cap, ntf_cap);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to bind to notification - %d\n", error);
    } else {
        sddf_dprintf("Success!\n");
    }

    sddf_deferred_notify(1);
}

struct pci_header_type1 *find_parent_pci_bridge(uintptr_t bus_base, uint8_t bus_start, uint8_t bus_end, uint8_t child_bus)
{
    struct pci_header_type1 *parent_bridge = NULL;

    for (uint8_t pci_bus = bus_start; pci_bus < bus_end; pci_bus++) {
        for (uint8_t pci_dev = 0; pci_dev < 32; pci_dev++) {
            for (uint8_t pci_func = 0; pci_func < 8; pci_func++) {
                struct pci_header_type1 *bridge_header = (struct pci_header_type1 *)(bus_base + (pci_bus << 20) + (pci_dev << 15) + (pci_func << 12));
                // Bits[6:0] - Header Layout specifying header type
                if ((bridge_header->header_type & 0x3F) == 1) {
                    sddf_dprintf("  - primary bus num: 0x%x\n", bridge_header->primary_bus_num);
                    sddf_dprintf("  - secondary bus num: 0x%x\n", bridge_header->secondary_bus_num);
                    sddf_dprintf("  - subordinate bus num: 0x%x\n", bridge_header->subordinate_bus_num);

                    if (parent_bridge == NULL) {
                        parent_bridge = bridge_header;
                        sddf_dprintf("update, header: 0x%lx, ecam_base: 0x%lx\n", (uintptr_t)bridge_header, bus_base);
                    } else {
                        if (bridge_header->secondary_bus_num >= parent_bridge->secondary_bus_num &&
                            bridge_header->subordinate_bus_num <= parent_bridge->subordinate_bus_num) {
                            sddf_dprintf("update\n");
                            parent_bridge = bridge_header;
                        }
                    }
                }
            }
        }
    }

    return parent_bridge;
}


// TODO: pass bus start and end as arguments
void pci_ecam_scan(uintptr_t bus_base, uint8_t bus_start, uint8_t bus_end)
{
    for (uint8_t pci_bus = bus_start; pci_bus < bus_end; pci_bus++) {
        for (uint8_t pci_dev = 0; pci_dev < 32; pci_dev++) {
            for (uint8_t pci_func = 0; pci_func < 8; pci_func++) {
                struct pci_header_type0 *pci_header = (struct pci_header_type0 *)(bus_base + (pci_bus << 20) + (pci_dev << 15) + (pci_func << 12));
                if (pci_header->vendor_id != 0xffff && pci_header->vendor_id != 0x0000) {
                    sddf_dprintf("bus: 0x%lx, dev: 0x%lx, func: 0x%lx, vendor_id: 0x%x, device_id: 0x%x, type: %u\n",
                                 (((uintptr_t)pci_header >> 20) & 0xff),
                                 (((uintptr_t)pci_header >> 15) & 0x1f),
                                 (((uintptr_t)pci_header >> 12) & 0x7),
                                 pci_header->vendor_id,
                                 pci_header->device_id,
                                 pci_header->header_type & 0x3F);
                }
                for (uint8_t k = 0; k < 6; k++) {
                    volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + (k * 0x04));
                    if (*mem_bar != 0xffffffff) {
                        sddf_dprintf("  BAR %d: 0x%x\n", k, *mem_bar);
                    }
                }

                // TODO: convert it to general solution
                if (pci_bus == 0 && pci_dev == 2 && pci_func == 0) {
                    struct pci_header_type1 *parent_bridge_header = find_parent_pci_bridge(bus_base, bus_start, bus_end, pci_bus);
                    sddf_dprintf("parent bridge: 0x%lx\n", (uintptr_t)parent_bridge_header);
                    pci_bridge_t *pci_bridge = find_pci_bridge((uintptr_t)parent_bridge_header, bus_base);
                    map_pci_bar(pci_header, 4, 0x60000000);
                    bind_irq(pci_bridge, pci_header, pci_bus, pci_dev, pci_func, 16);
                }

                /* if (pci_bus == 1 && pci_dev == 0 && pci_func == 0) { */
                /*     struct pci_header_type1 *parent_bridge_header = find_parent_pci_bridge(bus_base, bus_start, bus_end, pci_bus); */
                /*     sddf_dprintf("parent bridge: 0x%lx\n", (uintptr_t)parent_bridge_header); */
                /*     pci_bridge_t *pci_bridge = find_pci_bridge((uintptr_t)parent_bridge_header, bus_base); */
                /*     map_pci_bar(pci_header, 0, 0x2000000); */
                /*     bind_irq(pci_bridge, pci_header, pci_bus, pci_dev, pci_func, 16); */
                /* } */

            }
        }
    }
}

pci_bar_request_t read_bar_size(struct pci_header_type0 *pci_header, uint8_t bar_id)
{
    volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + (bar_id * 0x04));
    *mem_bar = 0;
    *mem_bar = 0xFFFFFFFF;
    uint64_t readback = (uint64_t)*mem_bar;

    uint8_t space_indicator = readback & 0x1;
    uint8_t bar_width = readback & 0x3;
    uint8_t prefetchable = readback & 0x1;
    uint64_t bar_size = (~(readback | 0xFFFFFFFF00000000) | 0xF) + 1;

    if (space_indicator == 0 && bar_width == 2) {
        volatile uint64_t *mem_bar_64b = (volatile uint64_t *)mem_bar;
        readback = *mem_bar_64b;
        bar_size = (~((uint64_t)readback) | 0xF) + 1;
    }

    pci_bar_request_t bar_request = {0, 0, 0, 0, 0};
    if (readback == 0) return bar_request;

    sddf_dprintf("    Space Indicator: %s\n", space_indicator == 1 ? "I/O" : "Memory");
    sddf_dprintf("    Prefetchable: %s\n", prefetchable ? "true" : "false");
    sddf_dprintf("    Width: %s\n", bar_width == 2 ? "64-bit BAR" : "32-bit BAR");

    if (space_indicator == 1) {
        if ((readback & 0xFFFF0000) == 0) {
            bar_size = (~(readback | 0xFFFFFFFFFFFF0000) | 0xF) + 1;
            bar_request.io_16bit = bar_size;
        } else {
            bar_request.io_32bit = bar_size;
        }
    } else {
        if (prefetchable == 1 && bar_width == 2) {
            bar_request.mem_64bit = bar_size;
        } else if (prefetchable == 1 && bar_width == 0) {
            bar_request.mem_32bit = bar_size;
        } else if (prefetchable == 0) {
            bar_request.mem_32bit_np = bar_size;
        }
    }
    sddf_dprintf("    Size: 0x%lx\n", bar_size);

    return bar_request;
}

pci_bar_request_t merge_bar_requests(pci_bar_request_t bar_request_a, pci_bar_request_t bar_request_b)
{
    pci_bar_request_t bar_request_merged;

    bar_request_merged.io_16bit = bar_request_a.io_16bit + bar_request_b.io_16bit;
    bar_request_merged.io_32bit = bar_request_a.io_32bit + bar_request_b.io_32bit;
    bar_request_merged.mem_32bit_np = bar_request_a.mem_32bit_np + bar_request_b.mem_32bit_np;
    bar_request_merged.mem_32bit = bar_request_a.mem_32bit + bar_request_b.mem_32bit;
    bar_request_merged.mem_64bit = bar_request_a.mem_64bit + bar_request_b.mem_64bit;

    return bar_request_merged;
}

pci_bar_request_t scan_and_calc_bar_size(uintptr_t host_bridge_base, pci_bridge_node_t *parent_bridge, uint8_t bus)
{
    pci_bar_request_t bar_request_summary = {0, 0, 0, 0, 0};
    pci_bridge_node_t *child = parent_bridge->child;
    for (uint8_t pci_dev = 0; pci_dev < 32; pci_dev++) {
        for (uint8_t pci_func = 0; pci_func < 8; pci_func++) {
            struct pci_header_type0 *pci_header = (struct pci_header_type0 *)(host_bridge_base + (bus << 20) + (pci_dev << 15) + (pci_func << 12));
            if (pci_header->vendor_id == 0xffff && pci_header->device_id == 0xffff) continue;

            sddf_dprintf("bus: 0x%lx, dev: 0x%lx, func: 0x%lx, vendor_id: 0x%x, device_id: 0x%x, type: %u\n",
                         (((uintptr_t)pci_header >> 20) & 0xff),
                         (((uintptr_t)pci_header >> 15) & 0x1f),
                         (((uintptr_t)pci_header >> 12) & 0x7),
                         pci_header->vendor_id,
                         pci_header->device_id,
                         pci_header->header_type & 0x3F);

            if (pci_header->header_type & 0x3F) {
                struct pci_header_type1 *bridge_header = (struct pci_header_type1 *)pci_header;
                sddf_dprintf("  - primary bus num: 0x%x\n", bridge_header->primary_bus_num);
                sddf_dprintf("  - secondary bus num: 0x%x\n", bridge_header->secondary_bus_num);
                sddf_dprintf("  - subordinate bus num: 0x%x\n", bridge_header->subordinate_bus_num);
                if (bridge_header->secondary_bus_num > bridge_header->subordinate_bus_num) {
                    continue;
                }

                uint32_t bridge_idx = num_pci_bridge_nodes;
                num_pci_bridge_nodes++;
                pci_bridge_nodes[bridge_idx].parent = parent_bridge;
                if (child) {
                    child->next = &pci_bridge_nodes[bridge_idx];
                    child = child->next;
                } else {
                    child = &pci_bridge_nodes[bridge_idx];
                    parent_bridge->child = child;
                }

                for (uint8_t child_bridge_bus = bridge_header->secondary_bus_num; child_bridge_bus <= bridge_header->subordinate_bus_num; child_bridge_bus++) {
                    pci_bar_request_t bar_request = scan_and_calc_bar_size(host_bridge_base, &pci_bridge_nodes[bridge_idx], child_bridge_bus);
                    bar_request_summary = merge_bar_requests(bar_request_summary, bar_request);
                }
            } else {
                for (uint8_t bar_id = 0; bar_id < 6; bar_id++) {
                    pci_bar_request_t bar_request = read_bar_size(pci_header, bar_id);
                    if (bar_request.mem_64bit > 0) {
                        bar_id++;
                    }
                    bar_request_summary = merge_bar_requests(bar_request_summary, bar_request);

                }
            }
        }
    }

    parent_bridge->total_req = bar_request_summary;
    sddf_dprintf("==Bus: %u\n", bus);
    sddf_dprintf("  - io_16bit: 0x%x\n", bar_request_summary.io_16bit);
    sddf_dprintf("  - io_32bit: 0x%x\n", bar_request_summary.io_32bit);
    sddf_dprintf("  - mem_32bit: 0x%x\n", bar_request_summary.mem_32bit);
    sddf_dprintf("  - mem_64bit: 0x%lx\n", bar_request_summary.mem_64bit);
    sddf_dprintf("  - mem_32bit_np: 0x%x\n", bar_request_summary.mem_32bit_np);
    return bar_request_summary;
}

bool alloc_from_resource_windows(pci_bridge_t *acpi_pci_bridge,
                                      enum device_resource_type resource_type,
                                      uintptr_t lower_boundary,
                                      uintptr_t upper_boundary,
                                      bool prefetchable,
                                      uint64_t size,
                                      uintptr_t *base)
{
    sddf_dprintf("Requested resource type 0x%x located within [0x%lx-0x%lx], prefetchable: %d, size: 0x%lx\n",
                 resource_type,
                 lower_boundary,
                 upper_boundary,
                 prefetchable,
                 size);
    sddf_dprintf("bridge: 0x%lx\n", (uintptr_t)acpi_pci_bridge);
    uint8_t num_res = acpi_pci_bridge->num_dev_resources;
    for (int j = 0; j < num_res; j++) {
        device_resource_t *dev_res = (device_resource_t *)&acpi_pci_bridge->dev_resources[j];
        /* sddf_dprintf("resource type: %u, min_addr: 0x%lx, max_addr: 0x%lx, type_flags: 0x%x\n", dev_res->type, dev_res->min_addr, dev_res->max_addr, dev_res->flags); */

        if (dev_res->type != resource_type) continue;
        if (lower_boundary > 0 && dev_res->max_addr < lower_boundary) continue;
        if (upper_boundary > 0 && dev_res->min_addr > upper_boundary) continue;

        // ACPI Release 6.5 Section 6.4.3.5.5 Resource Type Specific Flags
        //   Any value set in Bits[2:1] can be treated as `prefetchable`
        if (prefetchable && (dev_res->flags & 0x6) == 0) continue;
        if (!prefetchable && (dev_res->flags & 0x6)) continue;

        if (dev_res->max_addr - dev_res->min_addr < size) continue;

        *base = (uintptr_t)dev_res->min_addr + size;
        dev_res->min_addr = *base;
        return true;
    }

    return false;
}

bool alloc_resource_for_bridge(pci_bridge_node_t *pci_bridge, pci_bridge_t *acpi_pci_bridge)
{

    if (pci_bridge->parent && pci_bridge->parent->is_host_bridge == true) {
        pci_bar_request_t *req = &pci_bridge->total_req;
        uint32_t io_upper = 0x0; // Upper boundary of requested I/O end
        if (req->io_16bit > 0) {
            io_upper = 0x10000;
        }
        uint32_t io_size = (uint32_t)req->io_16bit + req->io_32bit;
        uintptr_t io_base = 0;
        sddf_dprintf("bridge: 0x%lx\n", (uintptr_t)acpi_pci_bridge);
        if (alloc_from_resource_windows(acpi_pci_bridge, ACPI_RES_TYPE_IO, 0x0, io_upper, false, io_size, &io_base)) {
            sddf_dprintf("[Error] failed to allocate 0x%x-byte I/O from resource windows\n", io_size);
            return false;
        }

        uint32_t mem_32bit_np_size = req->mem_32bit_np; // 32-bit non-prefetchable memory
        uint64_t mem_p_size = req->mem_64bit; // Prefetchable memory
        bool mem_p_is_64bit = false;
        uint64_t mem_p_upper = 0x0;
        uintptr_t mem_p_base = 0;
        uintptr_t mem_np_base = 0;
        if (req->mem_64bit > 0 && alloc_from_resource_windows(acpi_pci_bridge, ACPI_RES_TYPE_MEMORY, 0x100000000, 0x0, true, req->mem_64bit, &mem_p_base)) {
            // 32-bit memory is constrainted resource so prioritise merging 32bit prefetchable and non-prefetchable requests
            mem_32bit_np_size += req->mem_32bit;
            mem_p_is_64bit = true;
        } else if ((req->mem_32bit > 0 || req->mem_64bit > 0) && alloc_from_resource_windows(acpi_pci_bridge, ACPI_RES_TYPE_MEMORY, 0x0, 0x100000000, true, req->mem_64bit + req->mem_32bit, &mem_p_base)) {
            mem_p_size += req->mem_32bit;
        } else {
            mem_p_size = 0;
            mem_32bit_np_size += req->mem_32bit + req->mem_64bit;
        }

        if (!alloc_from_resource_windows(acpi_pci_bridge, ACPI_RES_TYPE_MEMORY, 0x0, 0x100000000, false, req->mem_64bit + req->mem_32bit, &mem_np_base)) {
            sddf_dprintf("[Error] failed to allocate 0x%x-byte memory from non-prefetchable windows\n", mem_32bit_np_size);
            return false;
        }

        pci_bridge->windows.io_base = io_base;
        pci_bridge->windows.io_limit = io_base + io_size;
        pci_bridge->windows.mem_np_base = mem_np_base;
        pci_bridge->windows.mem_np_limit = mem_np_base + mem_32bit_np_size;
        pci_bridge->windows.mem_p_base = mem_p_base;
        pci_bridge->windows.mem_p_limit = mem_p_base + mem_p_size;
        pci_bridge->windows.mem_p_is_64bit = mem_p_is_64bit;
        sddf_dprintf("==Allocate resource windows:\n");
        sddf_dprintf("  - io_base: 0x%x\n", pci_bridge->windows.io_base);
        sddf_dprintf("  - io_limit: 0x%x\n", pci_bridge->windows.io_limit);
        sddf_dprintf("  - mem_np_base: 0x%x\n", pci_bridge->windows.mem_np_base);
        sddf_dprintf("  - mem_np_limit: 0x%x\n", pci_bridge->windows.mem_np_limit);
        sddf_dprintf("  - mem_p_base: 0x%x\n", pci_bridge->windows.mem_p_base);
        sddf_dprintf("  - mem_p_limit: 0x%x\n", pci_bridge->windows.mem_p_limit);
        sddf_dprintf("  - mem_p_is_64bit: %u\n", pci_bridge->windows.mem_p_is_64bit);
    } else if (pci_bridge->is_host_bridge == true) {
        // Do nothing for host bridge
    } else {
        sddf_dprintf("[Error] nested bridges are not supported yet\n");
    }

    pci_bridge_node_t *child_bridge = pci_bridge->child;
    while (child_bridge) {
        alloc_resource_for_bridge(child_bridge, acpi_pci_bridge);
        child_bridge = child_bridge->next;
    }
}

void print_cnode_caps()
{
    sddf_dprintf("========Descriptions of received capabilities========\n");
    sddf_dprintf("cnode_caps start: %u, end: %u\n", cnode_specs->start, cnode_specs->end);
    sddf_dprintf("size of pci_resources_t: %lu\n", sizeof(pci_resources_t));
    sddf_dprintf("idx,   base_addr,  end_addr\n")
    sddf_dprintf("%3u: (IRQControl capability)\n", 1);
    for (int i = cnode_specs->start; i < cnode_specs->end; i++) {
        sddf_dprintf("%3u: 0x%09lx, 0x%09lx\n", i, cnode_specs->caps[i].base_addr, cnode_specs->caps[i].end_addr);
    }
}

void get_ut_by_paddr(uintptr_t target_paddr)
{
    for (int i = cnode_specs->start; i < cnode_specs->end; i++) {
        if (target_paddr >= cnode_specs->caps[i].base_addr && target_paddr < cnode_specs->caps[i].end_addr) {
            sddf_dprintf("Found the untyped %u containing the target physical address: 0x%lx\n", i, target_paddr);
        }
    }
}

void init(void)
{
    if (!acpi_ready) {
        sddf_dprintf("ACPI driver has not set things up. Waiting for signaling\n");
        return;
    }

    cnode_specs = (cnode_specs_t *)&pci_resources->cnode_specs;
    sddf_dprintf("cptr_pci_resources: 0x%lx\n", (uintptr_t)CPTR_CNODE_PCI_RESOURCES);
    sddf_dprintf("cptr_ethernet_driver: 0x%lx\n", (uintptr_t)CPTR_CSPACE_ETHERNET_DRIVER);
    cnode_specs->cptr = CPTR_CNODE_PCI_RESOURCES;

    sddf_dprintf("=========PCI driver is running==========\n");

    print_cnode_caps();

    for (int i = 0; i < pci_resources->num_pci_groups; i++) {
        sddf_dprintf("PCI segment group: %u, base addr: 0x%lx, bus_range: [%u-%u]\n",
                     pci_resources->pci_seg_groups[i].group_id,
                     pci_resources->pci_seg_groups[i].base_addr,
                     pci_resources->pci_seg_groups[i].bus_start,
                     pci_resources->pci_seg_groups[i].bus_end);
        pci_seg_group_t *pci_seg_group = &pci_resources->pci_seg_groups[i];
        /* pci_ecam_scan(pci_seg_group->base_addr, */
        /*              pci_seg_group->bus_start, */
        /*              pci_seg_group->bus_end); */
        uint32_t host_bridge_idx = num_pci_bridge_nodes;
        pci_bridge_nodes[host_bridge_idx].is_host_bridge = true;
        num_pci_bridge_nodes++;
        scan_and_calc_bar_size(pci_seg_group->base_addr, &pci_bridge_nodes[host_bridge_idx], pci_seg_group->bus_start);
        pci_bridge_t *host_bridge = find_pci_bridge(pci_seg_group->base_addr, pci_seg_group->base_addr);
        sddf_dprintf("host_bridge: 0x%lx\n", (uintptr_t)host_bridge);
        alloc_resource_for_bridge(&pci_bridge_nodes[0], host_bridge);
    }

    sddf_deferred_notify(1);
}

void notified(microkit_channel ch)
{
    sddf_dprintf("\n[PCI driver] notified by ch %d\n", ch);
    if (ch == 0 && !acpi_ready) {
        acpi_ready = true;
        init();
    }

}
