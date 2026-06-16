/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <microkit.h>
//#include <types.h>
#include <sel4/bootinfo_types.h>
#include <sel4/sel4_arch/mapping.h>
#include <sel4/sel4_arch/constants.h>

#include "acpi.h"

uintptr_t remaining_untypeds_vaddr;
typedef struct {
    /* seL4_CNode untyped_cnode_cptr; */
    seL4_SlotRegion untypeds;
    seL4_UntypedDesc untypedList[CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS];
} capDLBootInfo_t;

const char acpi_str_fadt[] = {'F', 'A', 'C', 'P', 0};
const char acpi_str_mcfg[] = {'M', 'C', 'F', 'G', 0};
const char acpi_str_hid[] = {'_', 'H', 'I', 'D', 0};  // Hardware ID
const char acpi_str_crs[] = {'_', 'C', 'R', 'S', 0};  // Current Resource Settings
const char acpi_str_prt[] = {'_', 'P', 'R', 'T', 0};  // PCI Routing Table
const char acpi_str_pic[] = {'_', 'P', 'I', 'C', 0};  // PIC mode method
const char eisaid_str_pcie[] = {'P', 'N', 'P', '0', 'A', '0', '8', 0};  // PCI Express Bus

capDLBootInfo_t *capDLBootInfo;
uintptr_t aml_object_pool_start = 0x30000000;
uintptr_t pci_resources_vaddr = 0x60000000;

seL4_CPtr vspace_cptr_pci_driver;
seL4_CPtr cnode_cptr_remaining_untypeds;
seL4_CPtr cnode_cptr_pci_resources;
uintptr_t bootinfo_remaining_untypeds;
uintptr_t bootinfo_rsdp;
seL4_CPtr cnode_pci_resources_free_slot = 1;
#define IDX_TO_CPTR(idx) (seL4_CPtr)(cnode_cptr_remaining_untypeds + idx)

scanner_t scanner;
aml_object_pool_t object_pool;
aml_object_t object_root;
pci_resources_t *pci_resources;
aml_object_t *lookup_results[100];
uint32_t lookup_cnt;

// TODO: let capDL initialiser create the PTs for ACPI

seL4_CPtr free_slot;
seL4_CPtr pdpt = 0;
seL4_CPtr pd = 1;
seL4_CPtr pt = 2;
seL4_CPtr frame = 3;
uintptr_t acpi_vaddr = 0x4000000;
uintptr_t acpi_dsdt_addr = 0x0;

#define MAX_NUM_RSDT_ENTRIES 2048
uint32_t acpi_rsdt_entries[MAX_NUM_RSDT_ENTRIES];

cap_desc_t cap_list[512];
uint32_t cap_list_start;
uint32_t cap_list_end;
cnode_caps_t *cnode_caps_pci_resources;
uint32_t kernel_objects_ut_idx;

acpi_copy_t acpi_tables_copy;

__attribute__((__section__(".test_dsdt_table"))) uint8_t test_dsdt_table[300000];
__attribute__((__section__(".test_ssdt_table"))) uint8_t test_ssdt_table[300000];
__attribute__((__section__(".test_mcfg_table"))) uint8_t test_mcfg_table[100];

// TODO: check if this makes sense to go to libsel4
// https://github.com/seL4/seL4_libs/blob/master/libsel4vka/arch_include/x86/vka/arch/object.h#L62
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
    seL4_Error error = seL4_Untyped_Retype(cnode_cptr_remaining_untypeds + ut_idx,
                                object_type,
                                size_bits,
                                cnode_cptr_remaining_untypeds, 0, 0,
                                cap_list_end, 1);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to retype an object type %lu, size_bits: %lu - error: %d\n", object_type, size_bits, error);
        return error;
    }

    /* sddf_dprintf("Retyped object type %lu, size_bits=%lu at 0x%lx to destination %d\n", object_type, size_bits, cap_list[ut_idx].base_addr, cap_list_end); */

    cap_list[cap_list_end].base_addr = cap_list[ut_idx].base_addr;
    cap_list[cap_list_end].end_addr = cap_list[ut_idx].base_addr + (1ULL << get_object_size(object_type, size_bits));
    cap_list[cap_list_end].object_type = object_type;
    cap_list[cap_list_end].object_type = cap_list[ut_idx].is_device;
    cap_list[cap_list_end].parent = ut_idx;
    cap_list[cap_list_end].child = 0;
    cap_list[cap_list_end].next = 0;
    cap_list[ut_idx].base_addr = cap_list[cap_list_end].end_addr;

    if (cap_list[ut_idx].child == 0) {
        cap_list[ut_idx].child = cap_list_end;
    } else {
        uint32_t child_ut_idx = cap_list[ut_idx].child;

        while (cap_list[child_ut_idx].next != 0) {
            child_ut_idx = cap_list[child_ut_idx].next;
        }
        cap_list[child_ut_idx].next = cap_list_end;
    }

    if (retyped_cptr_idx != NULL) {
        *retyped_cptr_idx = cap_list_end;
    }
    cap_list_end++;

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
    uint32_t ut_idx = cap_list_end;
    for (uint32_t i = cap_list_start; i < cap_list_end; i++) {
        if (cap_list[i].base_addr <= target_paddr && target_paddr < cap_list[i].end_addr && cap_list[i].object_type == seL4_UntypedObject) {
            ut_idx = i;
            break;
        }
    }
    if (ut_idx == cap_list_end) {
        sddf_dprintf("Error: Untyped containing physical address 0x%lx is not found\n", target_paddr);
        return seL4_InvalidArgument;
    }
    /* sddf_dprintf("Found the untyped containing physical address: 0x%lx\n", target_paddr); */
    /* sddf_dprintf("ut idx: %u, base_addr: 0x%lx, end_addr: 0x%lx\n", ut_idx, cap_list[ut_idx].base_addr, cap_list[ut_idx].end_addr); */

    seL4_Error error;

    // Divide untyped to smaller ones
    // TODO: figure out what's the maxinum and minimum bits here
    for (int bits = 63; bits >= 12; bits--) {
        while (target_paddr - cap_list[ut_idx].base_addr >= (1ULL << bits)) {
            error = untyped_retype(ut_idx, seL4_UntypedObject, bits, NULL);
            if (error != seL4_NoError){
                sddf_dprintf("Error: failed to divide an untyped(%d)[0x%lx-0x%lx] to a smaller untyped with size_bits=%d\n",
                             ut_idx,
                             cap_list[ut_idx].base_addr,
                             cap_list[ut_idx].end_addr,
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

    seL4_Word avai_mem_size = cap_list[target_ut_idx].end_addr - target_paddr;
    seL4_Word avai_mem_size_bits = max_size_bits(avai_mem_size);

    if (object_type != seL4_UntypedObject && avai_mem_size_bits < size_bits) {
        sddf_dprintf("Error: Untyped(%d)[0x%lx-0x%lx] has insufficient memory for (paddr: 0x%lx, size_bits: %lu)\n",
                     target_ut_idx,
                     cap_list[target_ut_idx].base_addr,
                     cap_list[target_ut_idx].end_addr,
                     target_paddr,
                     size_bits);
        return 0;
    }

    // Retype the target object
    return untyped_retype(target_ut_idx, object_type, size_bits, retyped_cptr_idx);
}

void clear_cap_list_entry(uint32_t ut_idx)
{
    cap_list[ut_idx].base_addr = 0;
    cap_list[ut_idx].end_addr = 0;
    cap_list[ut_idx].is_device = 0;
    cap_list[ut_idx].object_type = 0;
    cap_list[ut_idx].parent = 0;
    cap_list[ut_idx].child = 0;
}

bool update_cap_list_after_revoke(uint32_t ut_idx)
{
    if (cap_list[ut_idx].child) {
        uint32_t child_ut_idx = cap_list[ut_idx].child;
        uintptr_t base_addr = 0;
        uintptr_t end_addr = 0;
        while (child_ut_idx != 0) {
            bool success = update_cap_list_after_revoke(child_ut_idx);
            if (!success) {
                return success;
            }
            if (base_addr == end_addr) {
                base_addr = cap_list[child_ut_idx].base_addr;
                end_addr = cap_list[child_ut_idx].end_addr;
                clear_cap_list_entry(child_ut_idx);
            } else if (end_addr == cap_list[child_ut_idx].base_addr) {
                end_addr = cap_list[child_ut_idx].end_addr;
                clear_cap_list_entry(child_ut_idx);
            } else {
                sddf_dprintf("Error: something wrong during re-collecting untypeds\n");
                return false;
            }

            uint32_t child_cleared_idx = child_ut_idx;
            child_ut_idx = cap_list[child_ut_idx].next;
            cap_list[child_cleared_idx].next = 0;
        }

        if (end_addr != cap_list[ut_idx].base_addr) {
            sddf_dprintf("Error: something wrong during re-collecting untypeds\n");
            return false;
        }
        cap_list[ut_idx].base_addr = base_addr;
        cap_list[ut_idx].child = 0;
    }
    return true;
}

seL4_Error untypeds_revoke()
{
    for (uint32_t i = cap_list_end - 1; i >= cap_list_start; i--) {
        uint32_t parent_ut_idx = i;
        while (cap_list[parent_ut_idx].parent) {
            parent_ut_idx = cap_list[parent_ut_idx].parent;
        }

        // Revoke if this cap has been divided into small ones
        if (parent_ut_idx != i) {
            // TODO: proper way to calculate `depth`
            seL4_Error error = seL4_CNode_Revoke(cnode_cptr_remaining_untypeds, parent_ut_idx, 58);
            if (error != seL4_NoError) {
                return error;
            }

            bool success = update_cap_list_after_revoke(parent_ut_idx);
            if (!success) {
                return seL4_IllegalOperation;
            }
        }

        if (cap_list[i].end_addr == 0) {
            cap_list_end = i;
        }
    }

    return seL4_NoError;
}

seL4_Error pass_ut_with_range(uintptr_t min_addr, uintptr_t max_addr)
{
    uint32_t target_ut_idx;
    seL4_Error error = get_untyped_at_paddr(min_addr, &target_ut_idx);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to found the untyped containing physical address: 0x%lx\n", min_addr);
        return error;
    }

    seL4_Word avai_mem_size = cap_list[target_ut_idx].end_addr - min_addr;
    seL4_Word avai_mem_size_bits = max_size_bits(avai_mem_size);
    seL4_Word max_target_size_bits = max_size_bits(max_addr - min_addr);
    seL4_Word new_ut_size_bits = MIN(avai_mem_size_bits, max_target_size_bits);
    seL4_Word new_ut_size = (1ULL << new_ut_size_bits);

    uint32_t retyped_cptr_idx;
    /* sddf_dprintf("min_addr: 0x%lx, max_addr: 0x%lx\n", min_addr, max_addr); */
    error = untyped_retype(target_ut_idx, seL4_UntypedObject, new_ut_size_bits, &retyped_cptr_idx);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to retype an untyped [0x%lx-0x%lx] from an untyped(%d)[0x%lx-0x%lx]\n",
                     min_addr,
                     max_addr,
                     retyped_cptr_idx,
                     cap_list[retyped_cptr_idx].base_addr,
                     cap_list[retyped_cptr_idx].end_addr);
        return error;
    }

    // depth = guardSize + radixSize = 50 + 8 for CNode 'remaining_untypeds'
    error = seL4_CNode_Copy(cnode_cptr_pci_resources, cnode_pci_resources_free_slot, 58, cnode_cptr_remaining_untypeds, retyped_cptr_idx, 58, seL4_ReadWrite);
    /* error = seL4_CNode_Move(cnode_cptr_pci_resources, cnode_pci_resources_free_slot, 58, cnode_cptr_remaining_untypeds, retyped_cptr_idx, 58); */
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to copy a capability\n");
        return error;
    }
    /* sddf_dprintf("copy ut to slot %lu, start: %u, end: %u\n", cnode_pci_resources_free_slot, cnode_caps_pci_resources->start, cnode_caps_pci_resources->end); */

    cnode_caps_pci_resources->desc[cnode_caps_pci_resources->end].base_addr = min_addr;
    cnode_caps_pci_resources->desc[cnode_caps_pci_resources->end].end_addr = min_addr + new_ut_size;
    cnode_caps_pci_resources->end++;
    cnode_pci_resources_free_slot++;

    if (min_addr + new_ut_size < max_addr) {
        pass_ut_with_range(min_addr + new_ut_size, max_addr);
    }
    return seL4_NoError;
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

void pass_crs_and_caps(acpi_crs_list_t *crs_list, uint32_t bridge_idx)
{
    // TODO: deal with WORD_IO and WORD_BUS
    sddf_dprintf("=====pass CRS untypeds=====\n");
    while (crs_list) {
        uint8_t new_res_idx = pci_resources->bridges[bridge_idx].num_dev_resources;
        device_resource_t *dev_res = (device_resource_t *)&pci_resources->bridges[bridge_idx].dev_resources[new_res_idx];
        switch (crs_list->resource_type) {
            case WORD_AS_DESCRIPTOR: {
                acpi_word_address_space_t *word_as = (acpi_word_address_space_t *)crs_list->data_addr;
                dev_res->min_addr = word_as->min_address;
                dev_res->max_addr = word_as->min_address + word_as->address_length;

                switch (word_as->resource_type) {
                    case 0: {
                        dev_res->type = WORD_MEMORY;
                        pass_ut_with_range(dev_res->min_addr, dev_res->max_addr);
                        break;
                    }
                    case 1: {
                        dev_res->type = WORD_IO;
                        break;
                    }
                    case 2: {
                        dev_res->type = WORD_BUS;
                        break;
                    }
                }

                pci_resources->bridges[bridge_idx].num_dev_resources++;
                break;
            }
            case DWORD_AS_DESCRIPTOR: {
                acpi_dword_address_space_t *dword_as = (acpi_dword_address_space_t *)crs_list->data_addr;
                dev_res->min_addr = dword_as->min_address;
                dev_res->max_addr = dword_as->min_address + dword_as->address_length;

                switch (dword_as->resource_type) {
                    case 0: {
                        dev_res->type = DWORD_MEMORY;
                        pass_ut_with_range(dev_res->min_addr, dev_res->max_addr);
                        break;
                    }
                    case 1: {
                        dev_res->type = DWORD_IO;
                        break;
                    }
                    case 2: {
                        dev_res->type = DWORD_BUS;
                        break;
                    }
                }

                pci_resources->bridges[bridge_idx].num_dev_resources++;
                break;
            }
            case QWORD_AS_DESCRIPTOR: {
                acpi_qword_address_space_t *qword_as = (acpi_qword_address_space_t *)crs_list->data_addr;
                dev_res->min_addr = qword_as->min_address;
                dev_res->max_addr = qword_as->min_address + qword_as->address_length;

                switch (qword_as->resource_type) {
                    case 0: {
                        dev_res->type = QWORD_MEMORY;
                        pass_ut_with_range(dev_res->min_addr, dev_res->max_addr);
                        break;
                    }
                    case 1: {
                        dev_res->type = QWORD_IO;
                        break;
                    }
                    case 2: {
                        dev_res->type = QWORD_BUS;
                        break;
                    }
                }

                pci_resources->bridges[bridge_idx].num_dev_resources++;
                break;
            }
            default: {
                sddf_dprintf("Resource type 0x%02x parsing is not implemented\n", crs_list->resource_type);
            }
        }

        crs_list = crs_list->next;
    }
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

    /* sddf_dprintf("retyped and try mapping at vaddr: 0x%lx with ut idx: %u, 0x%lx\n", vaddr, retyped_cptr_idx, IDX_TO_CPTR(retyped_cptr_idx)); */
    error = map_frame(IDX_TO_CPTR(retyped_cptr_idx), vspace, vaddr, rights);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to map frame at vaddr: 0x%lx, err - %u\n", vaddr, error);
        return error;
    }

    return seL4_NoError;
}

// ========= Refactor =========
mempool_t aml_namespace_mempool;
aml_namespace_node_t namespace_root;

void init(void)
{

    capDLBootInfo = (capDLBootInfo_t*)bootinfo_remaining_untypeds;
    cap_list_start = capDLBootInfo->untypeds.start;
    // TODO: is end empty?
    for (uint32_t i = capDLBootInfo->untypeds.start; i < capDLBootInfo->untypeds.end; i++) {
        cap_list[i].base_addr = capDLBootInfo->untypedList[i].paddr;
        cap_list[i].end_addr = cap_list[i].base_addr + (1ULL << capDLBootInfo->untypedList[i].sizeBits);
        cap_list[i].is_device = capDLBootInfo->untypedList[i].isDevice;
        cap_list[i].object_type = seL4_UntypedObject;
        cap_list_end = i + 1;
    }

    // TODO: find a proper untyped for PT objects, not the first one is used by capDL initialiser
    uint32_t non_dev_mem_id = 0;
    for (uint32_t i = cap_list_start; i < cap_list_end; i++) {
        if (!cap_list[i].is_device) {
            if (non_dev_mem_id == 5) {
                kernel_objects_ut_idx = i;
                break;
            }
            non_dev_mem_id++;
        }
    }
    sddf_dprintf("Found an untyped for kernel objects: ut idx: 0x%x, paddr: 0x%lx\n", kernel_objects_ut_idx, cap_list[kernel_objects_ut_idx].base_addr);


    // Print summary
    sddf_dprintf("======MAP ======\n");
    pci_resources = (pci_resources_t *)pci_resources_vaddr;
    acpi_mcfg_t *mcfg_table = (acpi_mcfg_t *)&test_mcfg_table;
    uint32_t num_pci_seg_grps = (mcfg_table->header.length - sizeof(acpi_header_t)) / sizeof(pci_seg_group_t);
    sddf_dprintf("num_pci: %u\n", num_pci_seg_grps);
    for (int j = 0; j < num_pci_seg_grps; j++) {
        memcpy(&pci_resources->pci_seg_groups[pci_resources->num_pci_groups], &mcfg_table->pci_seg_group[j], sizeof(pci_seg_group_t));
        pci_resources->num_pci_groups++;
    }

    seL4_Error error;
    uintptr_t ecam_base_vaddr = 0x20000000;
    for (int i = 0; i < pci_resources->num_pci_groups; i++) {
        sddf_dprintf("PCI segment group: %u, base addr: 0x%lx, bus_range: [%u-%u]\n",
                     pci_resources->pci_seg_groups[i].group_id,
                     pci_resources->pci_seg_groups[i].base_addr,
                     pci_resources->pci_seg_groups[i].bus_start,
                     pci_resources->pci_seg_groups[i].bus_end);
        uint32_t ecam_size = (1 + pci_resources->pci_seg_groups[i].bus_end - pci_resources->pci_seg_groups[i].bus_start) * (1 << 20);
        uintptr_t end_paddr = pci_resources->pci_seg_groups[i].base_addr + ecam_size;
        uintptr_t cur_paddr = pci_resources->pci_seg_groups[i].base_addr;
        uintptr_t cur_vaddr = ecam_base_vaddr;
        while (cur_paddr < end_paddr) {
            error = retype_and_map_frame(cur_paddr, cur_vaddr, seL4_CapInitThreadVSpace, seL4_X86_LargePageObject, seL4_ReadWrite);
            if (error != seL4_NoError) {
                sddf_dprintf("Error: failed to retype or map a frame.\n");
                return;
            }
            cur_paddr += (1 << seL4_LargePageBits);
            cur_vaddr += (1 << seL4_LargePageBits);
        }

        pci_resources->pci_seg_groups[i].base_addr = ecam_base_vaddr;
        ecam_base_vaddr = cur_vaddr;
    }
    sddf_dprintf("Finished ECAM mapping!\n");

    sddf_dprintf("===============Scanning DSDT===============\n");

    acpi_dsdt_t *acpi_dsdt_table = (acpi_dsdt_t *)&test_dsdt_table;
    uint8_t *dsdt_copy_end = (uint8_t *)&test_dsdt_table + 299745;
    scanner.current = (uint8_t *)&acpi_dsdt_table->content[0];
    aml_namespace_mempool.start = (void *)aml_object_pool_start;
    aml_namespace_mempool.next = (void *)aml_object_pool_start;
    aml_namespace_mempool.end = (void *)aml_object_pool_start + 0x50000;
    sddf_dprintf("dsdt_table: 0x%lx, scanner.start: 0x%lx\n", (uintptr_t)&test_dsdt_table, (uintptr_t)scanner.current);

    /* uint8_t *dsdt_end = scanner.current + header->length - sizeof(acpi_header_t); */
    namespace_root.pkt_start = scanner.current;
    namespace_root.op_code = NULL_OP;
    namespace_root.name[0] = '\\';
    scan_namespace_tree(&namespace_root, dsdt_copy_end);

    sddf_dprintf("===============Scanning SSDT===============\n");
    acpi_dsdt_t *acpi_ssdt_table = (acpi_dsdt_t *)&test_ssdt_table;
    uint8_t *ssdt_copy_end = (uint8_t *)&test_ssdt_table + 12492;
    scanner.current = (uint8_t *)&acpi_ssdt_table->content[0];
    sddf_dprintf("ssdt_table: 0x%lx, scanner.start: 0x%lx\n", (uintptr_t)&test_ssdt_table, (uintptr_t)scanner.current);
    scan_namespace_tree(&namespace_root, ssdt_copy_end);


    aml_namespace_node_t *lookup_results[128];
    uint8_t num_results = find_decendant_nodes_by_name(&namespace_root, acpi_str_pic, lookup_results, 0);
    if (num_results == 0) {
        sddf_dprintf("[Error] namespace node \'%s\' is not found\n", acpi_str_pic);
        return;
    }
    sddf_dprintf("Found _PIC method! num: %u\n", num_results);

    uint8_t ret_buffer[100];
    uint64_t pic_method_arg = 1; // Enable APIC mode: pass 1 to method "_PIC"
    // TODO: fix ret_type
    eval_namespace_node(lookup_results[0], (uintptr_t)ret_buffer, 0, 1, &pic_method_arg);

    sddf_dprintf("===============Extract _CRS===============\n");

    num_results = find_decendant_nodes_by_name(&namespace_root, acpi_str_hid, lookup_results, 0);
    if (num_results == 0) {
        sddf_dprintf("[Error] namespace node \'%s\' is not found\n", acpi_str_pic);
        return;
    }
    for (uint32_t i = 0; i < num_results; i++) {
        aml_namespace_node_t *node = lookup_results[i];
        char eisa_id[10];
        read_eisa_id(node, eisa_id);
        if (!strcmp(eisa_id, eisaid_str_pcie)) {
            sddf_dprintf("=====Found PCIe Bus\n");
            aml_namespace_node_t *crs_node = find_child_node_by_name(node->parent, acpi_str_crs);
            if (crs_node == NULL) {
                sddf_dprintf("_CRS node is not found\n");
                return;
            }
            // TODO: fix ret_type
            eval_namespace_node(crs_node, (uintptr_t)ret_buffer, 0, 0, NULL);
            /* acpi_crs_list_t *crs_list = extract_pcie_crs(crs_node); */
            /* print_crs_list(crs_list); */
            /* return; */
            /* pass_crs_and_caps(crs_list, pci_resources->num_bridges); */
        }

    }

    /* seL4_Error error; */
    /* pci_resources = (pci_resources_t *)pci_resources_vaddr; */

    /* // TODO: extract RSDT according to revision */
    /* bootinfo_rsdp_t *bi_rsdp = (bootinfo_rsdp_t *)bootinfo_rsdp; */
    /* sddf_dprintf("revision: %d, rsdt_addr: 0x%x, xsdt_addr: 0x%lx\n", bi_rsdp->content.revision, bi_rsdp->content.rsdt_address, bi_rsdp->content.xsdt_address); */
    /* uintptr_t rsdt_addr = bi_rsdp->content.rsdt_address; */
    /* if (bi_rsdp->content.revision > 1) { */
    /*     rsdt_addr = bi_rsdp->content.xsdt_address; */
    /* } */

    /* // Map all the frames covering the RSDT table */
    /* uintptr_t rsdt_cur_paddr = rsdt_addr; */
    /* uint32_t rsdt_len = 1; */

    /* uint32_t rsdt_offset = rsdt_addr & 0xFFF; */
    /* volatile acpi_rsdt_t *acpi_rsdt = (acpi_rsdt_t *)(acpi_vaddr + rsdt_offset); */

    /* for (; rsdt_cur_paddr < rsdt_addr + rsdt_len; rsdt_cur_paddr += (1UL << seL4_PageBits)) { */
    /*     error = retype_and_map_frame(rsdt_cur_paddr, acpi_vaddr + rsdt_cur_paddr - rsdt_addr, seL4_CapInitThreadVSpace, seL4_X86_4K, seL4_CanRead); */
    /*     if (error != seL4_NoError) { */
    /*         sddf_dprintf("Error: failed to retype or map a frame.\n"); */
    /*         return; */
    /*     } */

    /*     if (rsdt_len == 1) { */
    /*         // TODO: validate */
    /*         sddf_dprintf("Signature: %c%c%c%c\n", */
    /*                      acpi_rsdt->header.signature[0], */
    /*                      acpi_rsdt->header.signature[1], */
    /*                      acpi_rsdt->header.signature[2], */
    /*                      acpi_rsdt->header.signature[3]); */
    /*         // TODO: edge case: length is in next page? */
    /*         rsdt_len = acpi_rsdt->header.length; */
    /*     } */
    /* } */

    /* // TODO: XSDT has different struct size */
    /* uint32_t entries = (acpi_rsdt->header.length - sizeof(acpi_rsdt->header)) / sizeof(uint32_t); */
    /* for (int i = 0; i < entries; i++) { */
    /*     acpi_rsdt_entries[i] = acpi_rsdt->entry[i]; */
    /* } */
    /* sddf_dprintf("entries: %d, rsdt_offset: 0x%x, length: %d\n", entries, rsdt_offset, acpi_rsdt->header.length); */
    /* error = untypeds_revoke(); */
    /* if (error != seL4_NoError) { */
    /*     sddf_dprintf("Error: failed to revoke the untypeds, err - %u\n", error); */
    /*     return; */
    /* } */

    /* for (int i = 0; i < entries; i++) { */
    /*     // TODO: edge cases? the struture acorss two pages? */
    /*     error = retype_and_map_frame(acpi_rsdt_entries[i], acpi_vaddr, seL4_CapInitThreadVSpace, seL4_X86_4K, seL4_CanRead); */
    /*     if (error != seL4_NoError) { */
    /*         sddf_dprintf("Error: failed to retype or map a frame.\n"); */
    /*         return; */
    /*     } */

    /*     acpi_header_t *header = (acpi_header_t *)(acpi_vaddr + (acpi_rsdt_entries[i] & 0xfff)); */

    /*     sddf_dprintf("Signature: %c%c%c%c\n", */
    /*              header->signature[0], */
    /*              header->signature[1], */
    /*              header->signature[2], */
    /*              header->signature[3]); */
    /*     sddf_dprintf("location: 0x%x, length: %d\n", acpi_rsdt_entries[i], header->length); */

    /*     if (strncmp(header->signature, acpi_str_fadt, 4) == 0) { */
    /*         sddf_dprintf("Found FADT table!\n"); */
    /*         acpi_fadt_t *fadt_table = (acpi_fadt_t *)header; */
    /*         sddf_dprintf("DSDT address: 0x%x\n", fadt_table->dsdt); */
    /*         acpi_dsdt_addr = fadt_table->dsdt; */
    /*     } else if (strncmp(header->signature, acpi_str_mcfg, 4) == 0) { */
    /*         sddf_dprintf("Found MCFG table!\n"); */

    /*         acpi_mcfg_t *mcfg_table = (acpi_mcfg_t *)header; */
    /*         uint32_t num_pci_seg_grps = (mcfg_table->header.length - sizeof(acpi_header_t)) / sizeof(pci_seg_group_t); */
    /*         for (int j = 0; j < num_pci_seg_grps; j++) { */
    /*             memcpy(&pci_resources->pci_seg_groups[pci_resources->num_pci_groups], &mcfg_table->pci_seg_group[j], sizeof(pci_seg_group_t)); */
    /*             pci_resources->num_pci_groups++; */
    /*         } */
    /*     } */

    /*     error = untypeds_revoke(); */
    /*     if (error != seL4_NoError) { */
    /*         sddf_dprintf("Error: failed to revoke the untypeds, err - %u\n", error); */
    /*         return; */
    /*     } */
    /* } */

    /* acpi_tables_copy.free_addr = 0x40000000; */
    /* acpi_tables_copy.end_addr = 0x40000000 + 0x50000; */

    /* uintptr_t dsdt_cur_paddr = acpi_dsdt_addr; */
    /* uint32_t dsdt_offset = acpi_dsdt_addr & 0xfff; */
    /* acpi_header_t *header = (acpi_header_t *)(acpi_vaddr + dsdt_offset); */
    /* uint32_t dsdt_len = 1; */

    /* for (; dsdt_cur_paddr < acpi_dsdt_addr + dsdt_len; dsdt_cur_paddr += (1UL << seL4_PageBits)) { */
    /*     error = retype_and_map_frame(dsdt_cur_paddr, acpi_vaddr + dsdt_cur_paddr - acpi_dsdt_addr, seL4_CapInitThreadVSpace, seL4_X86_4K, seL4_CanRead); */
    /*     if (error != seL4_NoError) { */
    /*         sddf_dprintf("Error: failed to retype or map a frame.\n"); */
    /*         return; */
    /*     } */

    /*     if (dsdt_len == 1) { */
    /*         dsdt_len = header->length; */
    /*         sddf_dprintf("Signature: %c%c%c%c\n", */
    /*                      header->signature[0], */
    /*                      header->signature[1], */
    /*                      header->signature[2], */
    /*                      header->signature[3]); */
    /*         sddf_dprintf("length: %d\n", header->length); */
    /*     } */
    /* } */

    /* uint8_t *copy_cur_vaddr = (uint8_t *)acpi_tables_copy.free_addr; */
    /* acpi_tables_copy.tables[0].type = ACPI_TABLE_TYPE_DSDT; */
    /* acpi_tables_copy.tables[0].base_addr = (uintptr_t)copy_cur_vaddr; */
    /* acpi_tables_copy.tables[0].length = header->length; */
    /* acpi_tables_copy.num_tables = 1; */

    /* uint8_t *dsdt_end = (uint8_t *)header + header->length; */
    /* sddf_dprintf("copy from start 0x%lx to 0x%lx\n", (uintptr_t)header, (uintptr_t)dsdt_end); */
    /* uint32_t k = 0; */
    /* for (uint8_t *dsdt_vaddr = (uint8_t *)header; dsdt_vaddr < dsdt_end; dsdt_vaddr++) { */
    /*     *copy_cur_vaddr = *dsdt_vaddr; */
    /*     copy_cur_vaddr++; */
    /* } */

    /* sddf_dprintf("===============Scanning DSDT===============\n"); */

    /* /\* acpi_dsdt_t *acpi_dsdt_table = (acpi_dsdt_t *)header; *\/ */
    /* /\* acpi_dsdt_t *acpi_dsdt_table = (acpi_dsdt_t *)acpi_tables_copy.tables[0].base_addr; *\/ */
    /* acpi_dsdt_t *acpi_dsdt_table = (acpi_dsdt_t *)&test_dsdt_table; */
    /* uint8_t *dsdt_copy_end = &test_dsdt_table + header->length; */
    /* scanner.current = (uint8_t *)&acpi_dsdt_table->content[0]; */
    /* object_pool.next = aml_object_pool_start; */
    /* object_pool.end = aml_object_pool_start + 0x30000; */
    /* sddf_dprintf("scanner.start: 0x%lx\n", (uintptr_t)scanner.current); */

    /* /\* uint8_t *dsdt_end = scanner.current + header->length - sizeof(acpi_header_t); *\/ */
    /* object_root.start = scanner.current; */
    /* object_root.op_code = NULL_OP; */
    /* object_root.name[0] = '\\'; */
    /* scan_objects(&object_root, dsdt_copy_end); */
    /* /\* print_object_tree(&object_root, 0); *\/ */

    /* sddf_dprintf("===========Pass IRQControl capability======\n"); */
    /* // depth = guardSize + radixSize = 50 + 8 for CNode 'remaining_untypeds' */
    /* // TODO: figure out why cannot copy the cap */
    /* /\* error = seL4_CNode_Copy(cnode_cptr_pci_resources, cnode_pci_resources_free_slot, 58, cnode_cptr_remaining_untypeds, 1, 58, seL4_ReadWrite); *\/ */
    /* error = seL4_CNode_Move(cnode_cptr_pci_resources, cnode_pci_resources_free_slot, 58, cnode_cptr_remaining_untypeds, 1, 58); */
    /* if (error) { */
    /*     sddf_dprintf("Error: failed to copy a capability\n"); */
    /*     return; */
    /* } */
    /* cnode_pci_resources_free_slot++; */

    /* non_dev_mem_id = 0; */
    /* uint32_t pci_kernel_objects_ut_idx = cap_list_end; */
    /* for (uint32_t i = cap_list_start; i < cap_list_end; i++) { */
    /*     if (!cap_list[i].is_device) { */
    /*         if (non_dev_mem_id == 8) { */
    /*             pci_kernel_objects_ut_idx = i; */
    /*             break; */
    /*         } */
    /*         non_dev_mem_id++; */
    /*     } */
    /* } */
    /* // @terryb: slot 1 for IRQ control, slot 2 for kernel objects */
    /* cnode_caps_pci_resources = (cnode_caps_t *)&pci_resources->cnode_caps; */
    /* cnode_caps_pci_resources->start = 3; */
    /* cnode_caps_pci_resources->end = 2; */
    /* if (pci_kernel_objects_ut_idx < cap_list_end) { */
    /*     pass_ut_with_range(cap_list[pci_kernel_objects_ut_idx].base_addr, cap_list[pci_kernel_objects_ut_idx].end_addr); */
    /* } */

    /* sddf_dprintf("===========Adjust PIC mode=========\n"); */
    /* lookup_cnt = 0; */
    /* query_all_objects_by_name(&object_root, acpi_str_pic); */
    /* // There should be only one PIC method */
    /* aml_object_t *pic_method = lookup_results[0]; */
    /* execute_method(pic_method, RET_TYPE_NONE, 1); */

    /* sddf_dprintf("===========Lookup Results=========\n"); */
    /* lookup_cnt = 0; */
    /* query_all_objects_by_name(&object_root, acpi_str_hid); */
    /* // TODO: get rid of lookup_list and return a list with all the parsed resources */
    /* for (uint32_t i = 0; i < lookup_cnt; i++) { */
    /*     aml_object_t *node = lookup_results[i]; */
    /*     char eisa_id[10]; */
    /*     read_eisa_id(node, eisa_id); */
    /*     if (!strcmp(eisa_id, eisaid_str_pcie)) { */
    /*         sddf_dprintf("Found PCIe Bus\n"); */

    /*         aml_object_t *crs_node = query_child_object_by_name(node->parent, acpi_str_crs); */
    /*         if (crs_node == NULL) { */
    /*             sddf_dprintf("_CRS node is not found\n"); */
    /*             return; */
    /*         } */
    /*         acpi_crs_list_t *crs_list = extract_pcie_crs(crs_node); */
    /*         print_crs_list(crs_list); */
    /*         return; */
    /*         pass_crs_and_caps(crs_list, pci_resources->num_bridges); */

    /*         aml_object_t *prt_node = query_child_object_by_name(node->parent, acpi_str_prt); */
    /*         if (prt_node == NULL) { */
    /*             sddf_dprintf("_PRT node is not found\n"); */
    /*             return; */
    /*         } */
    /*         aml_object_t *prt_package = (aml_object_t *)execute_method(prt_node, RET_TYPE_OBJECT, 0); */
    /*         extract_prt_package(prt_package, &pci_resources->bridges[pci_resources->num_bridges]); */
    /*         pci_resources->num_bridges++; */
    /*     } */
    /* } */

    /* // TODO: figure out a proper way to revoke used untypeds without affecting copied device memory */
    /* /\* error = untypeds_revoke(); *\/ */
    /* /\* if (error != seL4_NoError) { *\/ */
    /* /\*     sddf_dprintf("Error: failed to revoke the untypeds, err - %u\n", error); *\/ */
    /* /\*     return; *\/ */
    /* /\* } *\/ */

    /* // Print summary */
    /* sddf_dprintf("\n======PCI resources summary:======\n"); */
    /* uintptr_t ecam_base_vaddr = 0x50000000; */
    /* for (int i = 0; i < pci_resources->num_pci_groups; i++) { */
    /*     sddf_dprintf("PCI segment group: %u, base addr: 0x%lx, bus_range: [%u-%u]\n", */
    /*                  pci_resources->pci_seg_groups[i].group_id, */
    /*                  pci_resources->pci_seg_groups[i].base_addr, */
    /*                  pci_resources->pci_seg_groups[i].bus_start, */
    /*                  pci_resources->pci_seg_groups[i].bus_end); */
    /*     uint32_t ecam_size = (1 + pci_resources->pci_seg_groups[i].bus_end - pci_resources->pci_seg_groups[i].bus_start) * (1 << 20); */
    /*     uintptr_t end_paddr = pci_resources->pci_seg_groups[i].base_addr + ecam_size; */
    /*     uintptr_t cur_paddr = pci_resources->pci_seg_groups[i].base_addr; */
    /*     uintptr_t cur_vaddr = ecam_base_vaddr; */
    /*     while (cur_paddr < end_paddr) { */
    /*         error = retype_and_map_frame(cur_paddr, cur_vaddr, vspace_cptr_pci_driver, seL4_X86_LargePageObject, seL4_ReadWrite); */
    /*         if (error != seL4_NoError) { */
    /*             sddf_dprintf("Error: failed to retype or map a frame.\n"); */
    /*             return; */
    /*         } */
    /*         cur_paddr += (1 << seL4_LargePageBits); */
    /*         cur_vaddr += (1 << seL4_LargePageBits); */
    /*     } */

    /*     pci_resources->pci_seg_groups[i].base_addr = ecam_base_vaddr; */
    /*     ecam_base_vaddr = cur_vaddr; */
    /* } */
    /* sddf_dprintf("Finished ECAM mapping!\n"); */

    sddf_deferred_notify(0);
}

void notified(microkit_channel ch)
{
}
