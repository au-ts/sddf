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

uintptr_t pci_resources_vaddr = 0x60000000;
seL4_CPtr cnode_cptr_pci_resources;
pci_resources_t *pci_resources;
cnode_caps_t *cnode_caps;

bool acpi_ready = false;

// regions[1..] are used for MSI-X BARs
uint8_t avail_region_idx = 1;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".ecam_configs"))) pci_ecam_config_t pci_ecam_config;

/**
 * Look for the capability of a device by ID
 * */
static struct shared_pci_cap *find_pci_cap_by_id(struct pci_config_space *config_space, uint8_t cap_id)
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

void configure_pci_bar(struct pci_config_space *pci_header, uint8_t bar_id, pci_bar_t pci_bar_cfg)
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

void configure_irqs(struct pci_config_space *pci_header, config_request_t config_request)
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
                struct msix_capability *msix_cap = (struct msix_capability *)find_pci_cap_by_id(pci_header, PCI_CAP_ID_MSIX);
                if (msix_cap) {
                    // Bits 2-0 refer to BAR ID
                    uint8_t bar_id = msix_cap->table_offset_bir & 0x5;
                    pci_bar_t msix_bar;
                    msix_bar.bar_id = bar_id;
                    msix_bar.base_addr = device_resources.regions[avail_region_idx].io_addr;
                    msix_bar.ioport = false;

                    configure_pci_bar(pci_header, bar_id, msix_bar);

                    // Enable MSI-X
                    struct msix_msg_ctrl *msg_ctrl = &msix_cap->msg_ctrl;
                    msg_ctrl->msix_enable = 1;
                    sddf_dprintf("Table Size: 0x%x\n", msg_ctrl->table_size + 1);
                    sddf_dprintf("Function Mask: 0x%x\n", msg_ctrl->func_mask);
                    sddf_dprintf("MSI-X Enable: 0x%x\n", msg_ctrl->msix_enable);

                    struct msix_table *msix_table = (struct msix_table *)device_resources.regions[avail_region_idx].region.vaddr;
                    msix_table->msg_addr_low = 0xFEEu << 20;
                    msix_table->msg_data = 0x4030 + config_request.irqs[i].vector;
                    msix_table->vec_ctrl = 0x0;
                    sddf_dprintf("Vector 0 Message Addr Low: 0x%x\n", msix_table->msg_addr_low);
                    sddf_dprintf("Vector 0 Message Addr Hi: 0x%x\n", msix_table->msg_addr_hi);
                    sddf_dprintf("Vector 0 Message Data: 0x%x\n", msix_table->msg_data);
                    sddf_dprintf("Vector 0 Vector Control: 0x%x\n", msix_table->vec_ctrl);

                    uint32_t *msix_pba = (uint32_t *)(device_resources.regions[avail_region_idx].region.vaddr + 0x800);
                    sddf_dprintf("PBA: 0x%x\n", msix_pba[0]);

                    avail_region_idx += 1;
                } else {
                    sddf_dprintf("error: device does not support MSI-X\n");
                }
                break;
            };
        }

    }
}

// TODO: pass bus start and end as arguments
void pci_ecam_scan(uintptr_t bus_base, uint8_t bus_start, uint8_t bus_end)
{
    for (uint8_t pci_bus = bus_start; pci_bus < bus_end; pci_bus++) {
        for (uint8_t pci_dev = 0; pci_dev < 32; pci_dev++) {
            for (uint8_t pci_func = 0; pci_func < 8; pci_func++) {
                struct pci_config_space *pci_header = (struct pci_config_space *)(bus_base + (pci_bus << 20) + (pci_dev << 15) + (pci_func << 12));
                if (pci_header->vendor_id != 0xffff && pci_header->vendor_id != 0x0000) {
                    sddf_dprintf("bus: 0x%lx, dev: 0x%lx, func: 0x%lx, vedor_id: 0x%x, device_id: 0x%x\n",
                                 (((uintptr_t)pci_header >> 20) & 0xff),
                                 (((uintptr_t)pci_header >> 15) & 0x1f),
                                 (((uintptr_t)pci_header >> 12) & 0x7),
                                 pci_header->vendor_id,
                                 pci_header->device_id);
                }
            }
        }
    }
}

void print_cnode_caps()
{
    sddf_dprintf("========Descriptions of received capabilities========\n");
    sddf_dprintf("cnode_caps start: %lu, end: %lu\n", cnode_caps->start, cnode_caps->end);
    sddf_dprintf("size of pci_resources_t: %lu\n", sizeof(pci_resources_t));
    sddf_dprintf("idx,   base_addr,  end_addr\n")
    sddf_dprintf("%3u: (IRQControl capability)\n", 1);
    for (int i = cnode_caps->start; i < cnode_caps->end; i++) {
        sddf_dprintf("%3u: 0x%09lx, 0x%09lx\n", i, cnode_caps->desc[i].base_addr, cnode_caps->desc[i].end_addr);
    }
}

void get_ut_by_paddr(uintptr_t target_paddr)
{
    for (int i = cnode_caps->start; i < cnode_caps->end; i++) {
        if (target_paddr >= cnode_caps->desc[i].base_addr && target_paddr < cnode_caps->desc[i].end_addr) {
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
    cnode_caps = (cnode_caps_t *)&pci_resources->cnode_caps;

    sddf_dprintf("=========PCI driver is running==========\n");

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

    print_cnode_caps();

    sddf_dprintf("=========Descriptions of PCI resources==========\n");
    for (int i = 0; i < pci_resources->num_bridges; i++) {
        uint8_t num_res = pci_resources->bridges[i].num_dev_resources;
        sddf_dprintf("num_res: %u\n", num_res);
        for (int j = 0; j < num_res; j++) {
            device_resource_t *dev_res = (device_resource_t *)&pci_resources->bridges[i].dev_resources[j];
            sddf_dprintf("resource type: %u, min_addr: 0x%lx, max_addr: 0x%lx\n", dev_res->type, dev_res->min_addr, dev_res->max_addr);

            if (dev_res->type == DWORD_MEMORY || dev_res->type == WORD_MEMORY || dev_res->type == QWORD_MEMORY) {
                get_ut_by_paddr(dev_res->min_addr);
            }
        }
    }

    /* seL4_Error error = seL4_Untyped_Retype(cnode_cptr_pci_resources + 1, */
    /*                                        seL4_X86_LargePageObject, */
    /*                                        0, */
    /*                                        cnode_cptr_pci_resources, 0, 0, */
    /*                                        2, 1); */
    /* sddf_dprintf("error: %d\n", error); */

    sddf_dprintf("Try creating an IRQ handler capability: ");
    int ret = seL4_IRQControl_GetIOAPIC(cnode_cptr_pci_resources + 1, cnode_cptr_pci_resources, 250, 58, 0, 13, 0, 0, 13);
    if (ret) {
        sddf_dprintf("Error - %d\n", ret);
    } else {
        sddf_dprintf("Success!\n");
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
