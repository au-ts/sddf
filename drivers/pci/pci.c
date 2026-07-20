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

uintptr_t pci_resources_vaddr = 0x60000000;
seL4_CPtr cnode_cptr_pci_resources;
seL4_CPtr vspace_cptr_ethernet_driver;
pci_resources_t *pci_resources;
cnode_specs_t *cnode_specs;
uint32_t kernel_objects_ut_idx = 2;

seL4_CPtr cnode_cptr_ethernet_driver;

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

void configure_pci_bar(struct pci_header_type0 *pci_header, uint8_t bar_id, pci_bar_t pci_bar_cfg)
{
    sddf_dprintf("bar_id: %d, base_addr: 0x%lx\n", bar_id, pci_bar_cfg.base_addr);
    if (pci_bar_cfg.base_addr) {
            volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + (bar_id * 0x04));
            // TODO: check if the BAR type is matched
            sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
            *mem_bar = 0xFFFFFFFF;
            // TODO: read the size of BAR and allocate from the resource window
            //   and map it to the device driver's PD
            sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
            // TODO: write the allocated physical address to the BAR register
            *mem_bar = (uint32_t)pci_bar_cfg.base_addr;
            // TODO: check if it has been updated
            sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
    }
}

void map_pci_bar(struct pci_header_type0 *pci_header, uint8_t bar_id, uintptr_t target_vaddr)
{
    volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + (bar_id * 0x04));
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id + 1, mem_bar[1]);
    bool memory_64bit = (*mem_bar) & 0x4;
    uintptr_t dev_regs_paddr = *mem_bar;
    if (memory_64bit) {
        dev_regs_paddr = mem_bar[0] + ((uint64_t)mem_bar[1] << 32);
    }
    *mem_bar = 0xFFFFFFFF;
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id + 1, mem_bar[1]);
    uint32_t dev_regs_size = (~(*mem_bar) | 0xF) + 1;
    sddf_dprintf("size: 0x%x\n", dev_regs_size);
    // TODO: allocate memory region from the windows
    *mem_bar = dev_regs_paddr & 0xFFFFFFFF;
    if (memory_64bit) {
        *(mem_bar + 1) = dev_regs_paddr >> 32;
    }
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);


    seL4_Error error;
    uintptr_t cur_paddr = dev_regs_paddr;
    uintptr_t end_paddr = dev_regs_paddr + dev_regs_size;
    uintptr_t cur_vaddr = target_vaddr;
    seL4_CPtr test_idx;
    error = retype_at_paddr(cnode_specs, 0x0fd000000, seL4_UntypedObject, 10, &test_idx);
    return;

    while (cur_paddr < end_paddr) {
        error = retype_and_map_frame(cnode_specs, cur_paddr, cur_vaddr, vspace_cptr_ethernet_driver, seL4_X86_LargePageObject, seL4_ReadWrite);
        if (error != seL4_NoError) {
            sddf_dprintf("Error: failed to retype or map a frame.\n");
            return;
        }
        cur_paddr += (1 << seL4_LargePageBits);
        cur_vaddr += (1 << seL4_LargePageBits);
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

            if (dev_res->type == WORD_BUS) {
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

void bind_irq(struct pci_header_type0 *pci_header, uint8_t pci_bus, uint8_t pci_dev, uint8_t pci_func, uint8_t irq_num)
{
    uint8_t base_irq_cap = 138;
    uint8_t bridge_idx = get_pci_bridge_idx_by_bus(pci_bus);

    uint8_t num_prt_entries = pci_resources->bridges[bridge_idx].num_prt_entries;
    sddf_dprintf("num_prt_entries: %u\n", num_prt_entries);
    uint8_t gsi_number = 0;
    for (int j = 0; j < num_prt_entries; j++) {
        pci_prt_t *pci_prt = (pci_prt_t *)&pci_resources->bridges[bridge_idx].prt_entries[j];
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
    seL4_Error error = seL4_IRQControl_GetIOAPIC(cnode_cptr_pci_resources + 1, cnode_cptr_ethernet_driver, base_irq_cap + irq_num, 58, 0, gsi_number, 1, 0, 1);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to create an IO/APIC IRQ handler - %d\n", error);
    } else {
        sddf_dprintf("Success!\n");
    }

    sddf_dprintf("Try minting a notification capability: ");
    error = seL4_CNode_Mint(cnode_cptr_pci_resources, 250, 58, cnode_cptr_ethernet_driver, 1, 58, seL4_ReadWrite, 1 << irq_num);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to mint a notification - %d\n", error);
    } else {
        sddf_dprintf("Success!\n");
    }

    seL4_CPtr handler_cap = cnode_cptr_ethernet_driver + base_irq_cap + irq_num;
    seL4_CPtr ntf_cap = cnode_cptr_pci_resources + 250;

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
                        sddf_dprintf("update\n");
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


                // TODO: convert it to general solution
                /* if (pci_bus == 0 && pci_dev == 2 && pci_func == 0) { */
                /*     map_pci_bar(pci_header, 4); */
                /*     bind_irq(pci_header, pci_bus, pci_dev, pci_func, 16); */
                /* } */

                if (pci_bus == 1 && pci_dev == 0 && pci_func == 0) {
                    find_parent_pci_bridge(bus_base, bus_start, bus_end, pci_bus);
                    map_pci_bar(pci_header, 0, 0x2000000);
                    /* configure_msi() */
                    /* bind_irq(pci_header, pci_bus, pci_dev, pci_func, 16); */
                }

            }
        }
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

    pci_resources = (pci_resources_t *)pci_resources_vaddr;
    cnode_specs = (cnode_specs_t *)&pci_resources->cnode_specs;
    sddf_dprintf("cptr_pci_resources: 0x%lx\n", (uintptr_t)cnode_cptr_pci_resources);
    sddf_dprintf("cptr_ethernet_driver: 0x%lx\n", (uintptr_t)cnode_cptr_ethernet_driver);
    cnode_specs->cptr = cnode_cptr_pci_resources;

    sddf_dprintf("=========PCI driver is running==========\n");

    print_cnode_caps();

    for (int i = 0; i < pci_resources->num_pci_groups; i++) {
        sddf_dprintf("PCI segment group: %u, base addr: 0x%lx, bus_range: [%u-%u]\n",
                     pci_resources->pci_seg_groups[i].group_id,
                     pci_resources->pci_seg_groups[i].base_addr,
                     pci_resources->pci_seg_groups[i].bus_start,
                     pci_resources->pci_seg_groups[i].bus_end);
        pci_seg_group_t *pci_seg_group = &pci_resources->pci_seg_groups[i];
        pci_ecam_scan(pci_seg_group->base_addr,
                     pci_seg_group->bus_start,
                     pci_seg_group->bus_end);
    }

    /* sddf_dprintf("=========Descriptions of PCI resources==========\n"); */
    /* for (int i = 0; i < pci_resources->num_bridges; i++) { */
    /*     uint8_t num_res = pci_resources->bridges[i].num_dev_resources; */
    /*     sddf_dprintf("num_res: %u\n", num_res); */
    /*     for (int j = 0; j < num_res; j++) { */
    /*         device_resource_t *dev_res = (device_resource_t *)&pci_resources->bridges[i].dev_resources[j]; */
    /*         sddf_dprintf("resource type: %u, min_addr: 0x%lx, max_addr: 0x%lx\n", dev_res->type, dev_res->min_addr, dev_res->max_addr); */

    /*         if (dev_res->type == DWORD_MEMORY || dev_res->type == WORD_MEMORY || dev_res->type == QWORD_MEMORY) { */
    /*             get_ut_by_paddr(dev_res->min_addr); */
    /*         } */
    /*     } */

    /*     uint8_t num_prt_entries = pci_resources->bridges[i].num_prt_entries; */
    /*     sddf_dprintf("num_prt_entries: %u\n", num_prt_entries); */
    /*     for (int j = 0; j < num_prt_entries; j++) { */
    /*         pci_prt_t *pci_prt = (pci_prt_t *)&pci_resources->bridges[i].prt_entries[j]; */
    /*         sddf_dprintf("addr: 0x%X, pin: %u, gsi: %u\n", pci_prt->address, pci_prt->pin, pci_prt->gsi); */
    /*     } */
    /* } */


}

void notified(microkit_channel ch)
{
    sddf_dprintf("\n[PCI driver] notified by ch %d\n", ch);
    if (ch == 0 && !acpi_ready) {
        acpi_ready = true;
        init();
    }

}
