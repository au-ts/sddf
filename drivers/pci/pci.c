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
cnode_caps_t *cnode_caps;
uint32_t kernel_objects_ut_idx = 2;

seL4_CPtr cnode_cptr_ethernet_driver;

#define IDX_TO_CPTR(idx) (seL4_CPtr)(cnode_cptr_pci_resources + idx)
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

uint8_t get_object_size(seL4_Word object_type, seL4_Word size_bits)
{
    switch (object_type) {
    /* Generic objects. */
    case seL4_UntypedObject:
        return size_bits;
    case seL4_TCBObject:
        return seL4_TCBBits;
    case seL4_EndpointObject:
        return seL4_EndpointBits;
    case seL4_NotificationObject:
        return seL4_NotificationBits;
    case seL4_CapTableObject:
        return (seL4_SlotBits + size_bits);
    case seL4_X86_4K:
        return seL4_PageBits;
    case seL4_X86_LargePageObject:
        return seL4_LargePageBits;
    case seL4_X86_PageTableObject:
        return seL4_PageTableBits;
    case seL4_X86_PageDirectoryObject:
        return seL4_PageDirBits;
    default:
        // TODO: double-check this
        return size_bits;
    }
}

seL4_Error untyped_retype(uint32_t ut_idx,
                          seL4_Word object_type,
                          seL4_Word size_bits,
                          uint32_t *retyped_cptr_idx)
{
    seL4_Error error = seL4_Untyped_Retype(cnode_cptr_pci_resources + ut_idx,
                                object_type,
                                size_bits,
                                cnode_cptr_pci_resources, 0, 0,
                                cnode_caps->end, 1);
    if (error != seL4_NoError) {
        sddf_dprintf("ut: 0x%lx-0x%lx, idx: %u\n", cnode_caps->desc[ut_idx].base_addr, cnode_caps->desc[ut_idx].end_addr, ut_idx);
        sddf_dprintf("Error: failed to retype an object type %lu, size_bits: %lu - error: %d\n", object_type, size_bits, error);
        return error;
    }

    /* sddf_dprintf("Retyped object type %lu, size_bits=%lu at 0x%lx\n", object_type, size_bits, cnode_caps->desc[ut_idx].base_addr); */

    cnode_caps->desc[cnode_caps->end].base_addr = cnode_caps->desc[ut_idx].base_addr;
    cnode_caps->desc[cnode_caps->end].end_addr = cnode_caps->desc[ut_idx].base_addr + (1ULL << get_object_size(object_type, size_bits));
    cnode_caps->desc[cnode_caps->end].object_type = object_type;
    cnode_caps->desc[cnode_caps->end].object_type = cnode_caps->desc[ut_idx].is_device;
    cnode_caps->desc[cnode_caps->end].parent = ut_idx;
    cnode_caps->desc[cnode_caps->end].child = 0;
    cnode_caps->desc[cnode_caps->end].next = 0;
    cnode_caps->desc[ut_idx].base_addr = cnode_caps->desc[cnode_caps->end].end_addr;

    if (cnode_caps->desc[ut_idx].child == 0) {
        cnode_caps->desc[ut_idx].child = cnode_caps->end;
    } else {
        uint32_t child_ut_idx = cnode_caps->desc[ut_idx].child;

        while (cnode_caps->desc[child_ut_idx].next != 0) {
            child_ut_idx = cnode_caps->desc[child_ut_idx].next;
        }
        cnode_caps->desc[child_ut_idx].next = cnode_caps->end;
    }

    if (retyped_cptr_idx != NULL) {
        *retyped_cptr_idx = cnode_caps->end;
    }
    cnode_caps->end++;

    return seL4_NoError;
}

seL4_Word max_size_bits(seL4_Word size)
{
    seL4_Word i = 63;
    while (((1ULL << i) & size) == 0) {
        i--;
    }
    return i;
}

seL4_Error get_untyped_at_paddr(seL4_Word target_paddr,
                                uint32_t *target_ut_idx)
{
    uint32_t ut_idx = cnode_caps->end;
    for (uint32_t i = cnode_caps->start; i < cnode_caps->end; i++) {
        if (cnode_caps->desc[i].base_addr <= target_paddr && target_paddr < cnode_caps->desc[i].end_addr && cnode_caps->desc[i].object_type == seL4_UntypedObject) {
            ut_idx = i;
            break;
        }
    }
    if (ut_idx == cnode_caps->end) {
        sddf_dprintf("Error: Untyped containing physical address 0x%lx is not found\n", target_paddr);
        return seL4_InvalidArgument;
    }
    /* sddf_dprintf("Found the untyped containing physical address: 0x%lx\n", target_paddr); */
    /* sddf_dprintf("ut idx: %u, base_addr: 0x%lx, end_addr: 0x%lx\n", ut_idx, cnode_caps->desc[ut_idx].base_addr, cnode_caps->desc[ut_idx].end_addr); */

    seL4_Error error;

    // Divide untyped to smaller ones
    // TODO: figure out what's the maxinum and minimum bits here
    for (int bits = 63; bits >= 12; bits--) {
        while (target_paddr - cnode_caps->desc[ut_idx].base_addr >= (1ULL << bits)) {
            error = untyped_retype(ut_idx, seL4_UntypedObject, bits, NULL);
            if (error != seL4_NoError){
                sddf_dprintf("Error: failed to divide an untyped(%d)[0x%lx-0x%lx] to a smaller untyped with size_bits=%d\n",
                             ut_idx,
                             cnode_caps->desc[ut_idx].base_addr,
                             cnode_caps->desc[ut_idx].end_addr,
                             bits);
                return error;
            }
        }
    }

    *target_ut_idx = ut_idx;
    return seL4_NoError;
}

seL4_Error retype_at_paddr(seL4_Word target_paddr,
                           seL4_Word object_type,
                           seL4_Word size_bits,
                           uint32_t *retyped_cptr_idx)
{
    uint32_t target_ut_idx;
    seL4_Error error = get_untyped_at_paddr(target_paddr, &target_ut_idx);
    if (error != seL4_NoError) {
        return error;
    }

    seL4_Word avai_mem_size = cnode_caps->desc[target_ut_idx].end_addr - target_paddr;
    seL4_Word avai_mem_size_bits = max_size_bits(avai_mem_size);

    if (object_type != seL4_UntypedObject && avai_mem_size_bits < size_bits) {
        sddf_dprintf("Error: Untyped(%d)[0x%lx-0x%lx] has insufficient memory for (paddr: 0x%lx, size_bits: %lu)\n",
                     target_ut_idx,
                     cnode_caps->desc[target_ut_idx].base_addr,
                     cnode_caps->desc[target_ut_idx].end_addr,
                     target_paddr,
                     size_bits);
        return 0;
    }

    // Retype the target object
    /* sddf_dprintf("Retype object type: %lu\n", object_type); */
    return untyped_retype(target_ut_idx, object_type, size_bits, retyped_cptr_idx);
}

seL4_Error map_frame(seL4_CPtr frame_cap, seL4_CPtr vspace, uintptr_t vaddr, seL4_CapRights_t rights)
{
    seL4_Error err = seL4_X86_Page_Map(frame_cap, vspace, vaddr, rights, seL4_X86_Default_VMAttributes);

    for (int i = 0; i < 4 && err == seL4_FailedLookup; i++) {
        seL4_Word failed = seL4_MappingFailedLookupLevel();
        uint32_t retyped_cptr_idx;

        switch (failed) {
            case SEL4_MAPPING_LOOKUP_NO_PT: {
                err = untyped_retype(kernel_objects_ut_idx, seL4_X86_PageTableObject, 0, &retyped_cptr_idx);
                if (err != seL4_NoError) {
                    return err;
                }
                err = seL4_X86_PageTable_Map(IDX_TO_CPTR(retyped_cptr_idx), vspace, vaddr, seL4_X86_Default_VMAttributes);
                break;
            }
            case SEL4_MAPPING_LOOKUP_NO_PD: {
                err = untyped_retype(kernel_objects_ut_idx, seL4_X86_PageDirectoryObject, 0, &retyped_cptr_idx);
                if (err != seL4_NoError) {
                    return err;
                }
                err = seL4_X86_PageDirectory_Map(IDX_TO_CPTR(retyped_cptr_idx), vspace, vaddr, seL4_X86_Default_VMAttributes);
                break;
            }
            case SEL4_MAPPING_LOOKUP_NO_PDPT: {
                err = untyped_retype(kernel_objects_ut_idx, seL4_X86_PDPTObject, 0, &retyped_cptr_idx);
                if (err != seL4_NoError) {
                    return err;
                }
                err = seL4_X86_PDPT_Map(IDX_TO_CPTR(retyped_cptr_idx), vspace, vaddr, seL4_X86_Default_VMAttributes);
                break;
            }
        }

        if (err == seL4_NoError) {
            err = seL4_X86_Page_Map(frame_cap, vspace, vaddr, rights, seL4_X86_Default_VMAttributes);
        }
    }

    return err;
}

seL4_Error retype_and_map_frame(uintptr_t paddr, uintptr_t vaddr, seL4_CPtr vspace, seL4_Word page_type, seL4_CapRights_t rights)
{
    uint32_t retyped_cptr_idx;
    // TODO: round_down for large pages and check if it's a page type
    if (page_type == seL4_X86_4K) {
        paddr = ROUND_DOWN(paddr, 1UL << seL4_PageBits);
        vaddr = ROUND_DOWN(vaddr, 1UL << seL4_PageBits);
    } else if (page_type == seL4_X86_LargePageObject) {
        paddr = ROUND_DOWN(paddr, 1UL << seL4_LargePageBits);
        vaddr = ROUND_DOWN(vaddr, 1UL << seL4_LargePageBits);
    }
    seL4_Error error = retype_at_paddr(paddr, page_type, 0, &retyped_cptr_idx);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to retype at paddr 0x%lx\n", paddr);
        return error;
    }

    error = map_frame(IDX_TO_CPTR(retyped_cptr_idx), vspace, vaddr, rights);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to map frame at vaddr: 0x%lx, err - %u\n", vaddr, error);
        return error;
    }

    return seL4_NoError;
}

void map_pci_bar(struct pci_config_space *pci_header, uint8_t bar_id)
{
    volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + (bar_id * 0x04));
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
    uintptr_t dev_regs_paddr = *mem_bar;
    *mem_bar = 0xFFFFFFFF;
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
    uint32_t dev_regs_size = (~(*mem_bar) | 0xF) + 1;
    sddf_dprintf("size: 0x%x\n", dev_regs_size);
    *mem_bar = dev_regs_paddr;
    sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);

    seL4_Error error;
    uintptr_t cur_paddr = dev_regs_paddr;
    uintptr_t end_paddr = dev_regs_paddr + dev_regs_size;
    uintptr_t cur_vaddr = 0x60000000;
    while (cur_paddr < end_paddr) {
        error = retype_and_map_frame(cur_paddr, cur_vaddr, vspace_cptr_ethernet_driver, seL4_X86_4K, seL4_ReadWrite);
        if (error != seL4_NoError) {
            sddf_dprintf("Error: failed to retype or map a frame.\n");
            return;
        }
        cur_paddr += (1 << seL4_PageBits);
        cur_vaddr += (1 << seL4_PageBits);
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

                // TODO: convert it to general solution
                if (pci_bus == 0 && pci_dev == 2 && pci_func == 0) {
                    map_pci_bar(pci_header, 4);
                }
            }
        }
    }
}

void print_cnode_caps()
{
    sddf_dprintf("========Descriptions of received capabilities========\n");
    sddf_dprintf("cnode_caps start: %u, end: %u\n", cnode_caps->start, cnode_caps->end);
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

        uint8_t num_prt_entries = pci_resources->bridges[i].num_prt_entries;
        sddf_dprintf("num_prt_entries: %u\n", num_prt_entries);
        for (int j = 0; j < num_prt_entries; j++) {
            pci_prt_t *pci_prt = (pci_prt_t *)&pci_resources->bridges[i].prt_entries[j];
            sddf_dprintf("addr: 0x%X, pin: %u, gsi: %u\n", pci_prt->address, pci_prt->pin, pci_prt->gsi);
        }
    }

    uint8_t base_irq_cap = 138;
    uint8_t irq_num = 16;
    sddf_dprintf("Try creating an IRQ handler capability: ");
    seL4_Error error = seL4_IRQControl_GetIOAPIC(cnode_cptr_pci_resources + 1, cnode_cptr_ethernet_driver, base_irq_cap + irq_num, 58, 0, 0x16, 1, 0, 1);
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

void notified(microkit_channel ch)
{
    sddf_dprintf("\n[PCI driver] notified by ch %d\n", ch);
    if (ch == 0 && !acpi_ready) {
        acpi_ready = true;
        init();
    }

}
