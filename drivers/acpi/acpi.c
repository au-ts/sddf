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
const char eisaid_str_pcie[] = {'P', 'N', 'P', '0', 'A', '0', '8', 0};  // PCI Express Bus

capDLBootInfo_t *capDLBootInfo;
uintptr_t aml_object_pool_start;
uintptr_t pci_resource;

seL4_CPtr vspace_cptr_pci_driver;
seL4_CPtr cnode_cptr_remaining_untypeds;
seL4_CPtr cnode_cptr_pci_resources;
uintptr_t bootinfo_remaining_untypeds;
uintptr_t bootinfo_rsdp;

scanner_t scanner;
aml_object_pool_t object_pool;
aml_object_t object_root;
pci_resources_t pci_resources;
aml_object_t *lookup_results[50];
uint32_t lookup_cnt;

// TODO: let capDL initialiser create the PTs for ACPI

seL4_CPtr pdpt = 0;
seL4_CPtr pd = 1;
seL4_CPtr pt = 2;
seL4_CPtr frame = 3;
uintptr_t acpi_vaddr = 0x4000000;
uintptr_t acpi_dsdt_addr = 0x0;

#define MAX_NUM_RSDT_ENTRIES 2048
uint32_t acpi_rsdt_entries[MAX_NUM_RSDT_ENTRIES];


void map_pts(seL4_CPtr pt_untyped, seL4_CPtr cnode_cptr, seL4_CPtr free_slot) {

    seL4_Untyped_Retype(pt_untyped, seL4_X86_PDPTObject, 0, cnode_cptr, 0, 0, free_slot + pdpt, 1);
    seL4_Untyped_Retype(pt_untyped, seL4_X86_PageDirectoryObject, 0, cnode_cptr, 0, 0, free_slot + pd, 1);
    seL4_Untyped_Retype(pt_untyped, seL4_X86_PageTableObject, 0, cnode_cptr, 0, 0, free_slot + pt, 1);

    seL4_X86_PDPT_Map(cnode_cptr + free_slot + pdpt, seL4_CapInitThreadVSpace, acpi_vaddr, seL4_X86_Default_VMAttributes);
    seL4_X86_PageDirectory_Map(cnode_cptr + free_slot + pd, seL4_CapInitThreadVSpace, acpi_vaddr, seL4_X86_Default_VMAttributes);
    seL4_X86_PageTable_Map(cnode_cptr + free_slot + pt, seL4_CapInitThreadVSpace, acpi_vaddr, seL4_X86_Default_VMAttributes);
}

seL4_Error retype_at_offset(seL4_CPtr parent_untyped,
                            seL4_Word parent_paddr,
                            seL4_CPtr cnode_cptr,
                            seL4_Word target_paddr,
                            seL4_Word page_object,
                            seL4_CPtr *free_slots)
{
    seL4_Error error;
    seL4_Word current_paddr = parent_paddr;
    seL4_Word remaining_offset = target_paddr - parent_paddr;

    sddf_dprintf("untyped: 0x%lx, paddr: 0x%lx, target: 0x%lx\n", parent_untyped, parent_paddr, target_paddr);
    // 1. Divide preceding memory into smaller Untypeds
    // We iterate from 30 (1GB) down to 12 (4KB)
    for (int bits = 30; bits >= 12; bits--) {
        seL4_Word size = (1UL << bits);

        while (remaining_offset >= size) {
            // Create a "filler" Untyped to move the allocation pointer forward
            sddf_dprintf("bits: %d\n", bits);
            error = seL4_Untyped_Retype(parent_untyped,
                                        seL4_UntypedObject,
                                        bits,
                                        cnode_cptr, 0, 0,
                                        *free_slots, 1);
            if (error != seL4_NoError) return error;

            (*free_slots)++; // Use next slot
            remaining_offset -= size;
            current_paddr += size;
            sddf_dprintf("create untyped size bits: %d at 0x%lx\n", bits, current_paddr - size);
        }
    }

    // 2. Now the parent Untyped's internal pointer is at target_paddr
    // Retype the actual Frame
    error = seL4_Untyped_Retype(parent_untyped,
                                page_object,
                                0,
                                cnode_cptr, 0, 0,
                                *free_slots, 1);

    if (error == seL4_NoError) {
        sddf_dprintf("create frame at: 0x%lx\n", current_paddr);
    }

    return error;
}

uint32_t find_untyped_id_by_paddr(uintptr_t paddr)
{
    for (uint32_t i = capDLBootInfo->untypeds.start; i < capDLBootInfo->untypeds.end; i++) {
        // TODO: map the frame if included in this untyped
        uintptr_t untyped_end = capDLBootInfo->untypedList[i].paddr + (1 << capDLBootInfo->untypedList[i].sizeBits);
        if (capDLBootInfo->untypedList[i].paddr <= paddr && paddr < untyped_end) {
            return i;
        }
    }

    return capDLBootInfo->untypeds.end;
}

seL4_Error map_frame(seL4_CPtr obj_ut_cap, seL4_CPtr frame_cap, seL4_CPtr vspace, uintptr_t vaddr, seL4_CapRights_t rights, seL4_CPtr cnode_cptr, seL4_CPtr *free_slots)
{
    seL4_Error err = seL4_X86_Page_Map(frame_cap, vspace, vaddr, rights, seL4_X86_Default_VMAttributes);

    for (int i = 0; i < 4 && err == seL4_FailedLookup; i++) {
        seL4_Word failed = seL4_MappingFailedLookupLevel();

        switch (failed) {
        case SEL4_MAPPING_LOOKUP_NO_PT:
            err = seL4_Untyped_Retype(obj_ut_cap, seL4_X86_PageTableObject, 0, cnode_cptr, 0, 0, *free_slots, 1);
            if (err) {
                return err;
            }
            err = seL4_X86_PageTable_Map(cnode_cptr + *free_slots, vspace, vaddr, seL4_X86_Default_VMAttributes);
            break;
        case SEL4_MAPPING_LOOKUP_NO_PD:
            err = seL4_Untyped_Retype(obj_ut_cap, seL4_X86_PageDirectoryObject, 0, cnode_cptr, 0, 0, *free_slots, 1);
            if (err) {
                return err;
            }
            err = seL4_X86_PageDirectory_Map(cnode_cptr + *free_slots, vspace, vaddr, seL4_X86_Default_VMAttributes);
            break;
        case SEL4_MAPPING_LOOKUP_NO_PDPT:
            err = seL4_Untyped_Retype(obj_ut_cap, seL4_X86_PDPTObject, 0, cnode_cptr, 0, 0, *free_slots, 1);
            if (err) {
                return err;
            }
            err = seL4_X86_PDPT_Map(cnode_cptr + *free_slots, vspace, vaddr, seL4_X86_Default_VMAttributes);
            break;
        }

        if (!err) {
            free_slots++;
            err = seL4_X86_Page_Map(frame_cap, vspace, vaddr, rights, seL4_X86_Default_VMAttributes);
        }
    }

    return err;
}

void init(void)
{
    // TODO: probably should use Bill's patch for prefilling memory regions
    // TODO: extract RSDT according to revision
    bootinfo_rsdp_t *bi_rsdp = (bootinfo_rsdp_t *)bootinfo_rsdp;
    sddf_dprintf("revision: %d, rsdt_addr: 0x%x, xsdt_addr: 0x%lx\n", bi_rsdp->content.revision, bi_rsdp->content.rsdt_address, bi_rsdp->content.xsdt_address);
    uintptr_t rsdt_addr = bi_rsdp->content.rsdt_address;


    sddf_dprintf("MAX_NUM_UNTYPEDS: %d\n", CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS);

    capDLBootInfo = (capDLBootInfo_t*)bootinfo_remaining_untypeds;
    sddf_dprintf("untyped_cnode_cptr: 0x%lx\n", cnode_cptr_remaining_untypeds);

    uint32_t ut_pt_idx = 0;
    uint32_t non_dev_mem_id = 0;

    sddf_dprintf("untypeds start: %lu, end: %lu\n", capDLBootInfo->untypeds.start, capDLBootInfo->untypeds.end);

    for (uint32_t i = capDLBootInfo->untypeds.start; i < capDLBootInfo->untypeds.end; i++) {
        sddf_dprintf("i: %d, paddr: 0x%lx, sizeBits: %d, isDevice: %d\n", i, capDLBootInfo->untypedList[i].paddr, capDLBootInfo->untypedList[i].sizeBits, capDLBootInfo->untypedList[i].isDevice);
        if (!capDLBootInfo->untypedList[i].isDevice) {
            // TODO: find a proper untyped for PT objects, not the first one is used by capDL initialiser
            if (non_dev_mem_id == 5) {
                ut_pt_idx = i;
                break;
            }
            non_dev_mem_id++;
        }
    }
    sddf_dprintf("untyped pt idx: 0x%x, paddr: 0x%lx\n", ut_pt_idx, capDLBootInfo->untypedList[ut_pt_idx].paddr);

    sddf_dprintf("rsdt_addr: 0x%lx\n", rsdt_addr);
    uint32_t acpi_ut_idx = find_untyped_id_by_paddr(rsdt_addr);
    sddf_dprintf("acpi ut idx: %d\n", acpi_ut_idx);

    sddf_dprintf("ut paddr: 0x%lx\n", capDLBootInfo->untypedList[acpi_ut_idx].paddr);
    map_pts(cnode_cptr_remaining_untypeds + ut_pt_idx, cnode_cptr_remaining_untypeds, capDLBootInfo->untypeds.end);

    sddf_dprintf("PT mapping finished\n");
    seL4_CPtr free_slot = capDLBootInfo->untypeds.end + frame + 1;
    retype_at_offset(cnode_cptr_remaining_untypeds + acpi_ut_idx,
                     capDLBootInfo->untypedList[acpi_ut_idx].paddr,
                     cnode_cptr_remaining_untypeds,
                     rsdt_addr, seL4_X86_4K, &free_slot);

    seL4_Error error = seL4_X86_Page_Map(cnode_cptr_remaining_untypeds + free_slot, seL4_CapInitThreadVSpace, acpi_vaddr,
                              seL4_CanRead,
                              seL4_X86_Default_VMAttributes);

    if (error != seL4_NoError) {
        sddf_dprintf("Failed to map frame\n");
    }

    uint32_t rsdt_offset = rsdt_addr & 0xFFF;
    volatile acpi_rsdt_t *acpi_rsdt = (acpi_rsdt_t *)(acpi_vaddr + rsdt_offset);

    // TODO: validate
    sddf_dprintf("Signature: %c%c%c%c\n",
                 acpi_rsdt->header.signature[0],
                 acpi_rsdt->header.signature[1],
                 acpi_rsdt->header.signature[2],
                 acpi_rsdt->header.signature[3]);

    seL4_Word acpi_ut_paddr;
    // Map all the frames covering the RSDT table
    for (int i = 1; i * 4096 < rsdt_offset + acpi_rsdt->header.length; i++) {
        uint32_t following_acpi_ut_idx = find_untyped_id_by_paddr(rsdt_addr + i * 4096);
        free_slot++;

        if (following_acpi_ut_idx == acpi_ut_idx) {
            acpi_ut_paddr =  rsdt_addr + i * 4096;
        } else {
            acpi_ut_paddr = capDLBootInfo->untypedList[following_acpi_ut_idx].paddr;
        }

        sddf_dprintf("map %d-th page\n", i);
        retype_at_offset(cnode_cptr_remaining_untypeds + following_acpi_ut_idx,
                         acpi_ut_paddr,
                         cnode_cptr_remaining_untypeds,
                         rsdt_addr + i * 4096, seL4_X86_4K, &free_slot);

        seL4_X86_Page_Map(cnode_cptr_remaining_untypeds + free_slot,
                          seL4_CapInitThreadVSpace,
                          acpi_vaddr + i * 4096,
                          seL4_CanRead,
                          seL4_X86_Default_VMAttributes);
    }

    // TODO: XSDT has different struct size
    uint32_t entries = (acpi_rsdt->header.length - sizeof(acpi_rsdt->header)) / sizeof(uint32_t);
    sddf_dprintf("entries: %d, rsdt_offset: 0x%x, length: %d\n", entries, rsdt_offset, acpi_rsdt->header.length);

    for (int i = 0; i < entries; i++) {
        acpi_rsdt_entries[i] = acpi_rsdt->entry[i];
    }

    // depth = guard_size(50) + size_bits(8)
    error = seL4_CNode_Revoke(cnode_cptr_remaining_untypeds, acpi_ut_idx, 58);
    sddf_dprintf("Error: %d\n", error);

    free_slot = capDLBootInfo->untypeds.end + frame + 1;

    for (int i = 0; i < entries; i++) {
        acpi_ut_idx = find_untyped_id_by_paddr(acpi_rsdt_entries[i]);
        retype_at_offset(cnode_cptr_remaining_untypeds + acpi_ut_idx,
                         capDLBootInfo->untypedList[acpi_ut_idx].paddr,
                         cnode_cptr_remaining_untypeds,
                         acpi_rsdt_entries[i], seL4_X86_4K, &free_slot);

        error = seL4_X86_Page_Map(cnode_cptr_remaining_untypeds + free_slot, seL4_CapInitThreadVSpace, acpi_vaddr,
                              seL4_CanRead,
                              seL4_X86_Default_VMAttributes);

        acpi_header_t *header = (acpi_header_t *)(acpi_vaddr + (acpi_rsdt_entries[i] & 0xfff));

        sddf_dprintf("Signature: %c%c%c%c\n",
                 header->signature[0],
                 header->signature[1],
                 header->signature[2],
                 header->signature[3]);
        sddf_dprintf("location: 0x%x, length: %d\n", acpi_rsdt_entries[i], header->length);

        if (strncmp(header->signature, acpi_str_fadt, 4) == 0) {
            sddf_dprintf("Found FADT table!\n");
            acpi_fadt_t *fadt_table = (acpi_fadt_t *)header;
            sddf_dprintf("DSDT address: 0x%x\n", fadt_table->dsdt);
            acpi_dsdt_addr = fadt_table->dsdt;
        } else if (strncmp(header->signature, acpi_str_mcfg, 4) == 0) {
            sddf_dprintf("Found MCFG table!\n");

            acpi_mcfg_t *mcfg_table = (acpi_mcfg_t *)header;
            uint32_t num_pci_seg_grps = (mcfg_table->header.length - sizeof(acpi_header_t)) / sizeof(pci_seg_group_t);
            for (int j = 0; j < num_pci_seg_grps; j++) {
                memcpy(&pci_resources.pci_seg_groups[pci_resources.num_pci_groups], &mcfg_table->pci_seg_group[j], sizeof(pci_seg_group_t));
                pci_resources.num_pci_groups++;
            }

        }

        error = seL4_CNode_Revoke(cnode_cptr_remaining_untypeds, acpi_ut_idx, 58);
        sddf_dprintf("Error: %d\n", error);
        sddf_dprintf("\n=====================\n");
    }


    free_slot = capDLBootInfo->untypeds.end + frame + 1;
    // Parse DSDT table
    acpi_ut_idx = find_untyped_id_by_paddr(acpi_dsdt_addr);
    retype_at_offset(cnode_cptr_remaining_untypeds + acpi_ut_idx,
                     capDLBootInfo->untypedList[acpi_ut_idx].paddr,
                     cnode_cptr_remaining_untypeds,
                     acpi_dsdt_addr, seL4_X86_4K, &free_slot);

    error = seL4_X86_Page_Map(cnode_cptr_remaining_untypeds + free_slot, seL4_CapInitThreadVSpace, acpi_vaddr,
                          seL4_CanRead,
                          seL4_X86_Default_VMAttributes);

    uint32_t dsdt_offset = acpi_dsdt_addr & 0xfff;
    acpi_header_t *header = (acpi_header_t *)(acpi_vaddr + dsdt_offset);
    sddf_dprintf("Signature: %c%c%c%c\n",
             header->signature[0],
             header->signature[1],
             header->signature[2],
             header->signature[3]);
    sddf_dprintf("length: %d\n", header->length);


    // Map all the frames covering the DSDT table
    for (int i = 1; i * 4096 < dsdt_offset + header->length; i++) {
        uint32_t following_acpi_ut_idx = find_untyped_id_by_paddr(acpi_dsdt_addr + i * 4096);
        free_slot++;

        if (following_acpi_ut_idx == acpi_ut_idx) {
            acpi_ut_paddr =  acpi_dsdt_addr + i * 4096;
        } else {
            acpi_ut_paddr = capDLBootInfo->untypedList[following_acpi_ut_idx].paddr;
        }

        sddf_dprintf("map %d-th page at paddr 0x%lx, ut_paddr: 0x%lx\n", i, acpi_dsdt_addr + 1 * 4096, acpi_ut_paddr);
        retype_at_offset(cnode_cptr_remaining_untypeds + following_acpi_ut_idx,
                         acpi_ut_paddr,
                         cnode_cptr_remaining_untypeds,
                         acpi_dsdt_addr + i * 4096, seL4_X86_4K, &free_slot);

        seL4_X86_Page_Map(cnode_cptr_remaining_untypeds + free_slot,
                          seL4_CapInitThreadVSpace,
                          acpi_vaddr + i * 4096,
                          seL4_CanRead,
                          seL4_X86_Default_VMAttributes);
    }


    sddf_dprintf("===============Scanning DSDT===============\n");

    acpi_dsdt_t *acpi_dsdt_table = (acpi_dsdt_t *)header;
    scanner.current = (uint8_t *)&acpi_dsdt_table->content[0];
    object_pool.next = aml_object_pool_start;
    object_pool.end = aml_object_pool_start + 0x10000;
    sddf_dprintf("scanner.start: 0x%lx\n", (uintptr_t)scanner.current);

    uint8_t *dsdt_end = scanner.current + header->length - sizeof(acpi_header_t);
    object_root.start = scanner.current;
    object_root.op_code = NULL_OP;
    object_root.name[0] = '\\';
    scan_objects(&object_root, dsdt_end);
    print_object_tree(&object_root, 0);

    sddf_dprintf("===========Lookup Results=========\n");
    lookup_cnt = 0;
    query_all_objects_by_name(&object_root, acpi_str_hid);
    // TODO: get rid of lookup_list and return a list with all the parsed resources
    for (uint32_t i = 0; i < lookup_cnt; i++) {
        aml_object_t *node = lookup_results[i];
        char eisa_id[10];
        read_eisa_id(node, eisa_id);
        if (!strcmp(eisa_id, eisaid_str_pcie)) {
            sddf_dprintf("Found PCIe Bus\n");

            aml_object_t *crs_node = query_child_object_by_name(node->parent, acpi_str_crs);
            if (crs_node == NULL) {
                sddf_dprintf("_CRS node is not found\n");
                return;
            }
            acpi_crs_list_t *crs_list = extract_pcie_crs(crs_node);
            print_crs_list(crs_list);

            aml_object_t *prt_node = query_child_object_by_name(node->parent, acpi_str_prt);
            if (prt_node == NULL) {
                sddf_dprintf("_PRT node is not found\n");
                return;
            }
            char package_name[5];
            if (extract_pcie_prt(prt_node, package_name)) {
                sddf_dprintf("Routing table package \'%s'\n", package_name);
                aml_object_t *prt_package = query_same_domain_object_by_name(node, package_name);
                if (prt_package) {
                    sddf_dprintf("Found PRT package location: 0x%lx\n", (uintptr_t)prt_package->start);
                    extract_prt_package(prt_package);
                } else {
                    sddf_dprintf("PRT package is not found\n");
                }
            } else {
                sddf_dprintf("Failed to parse the package name for routing tables\n");
            }
        }
    }

    /* error = seL4_CNode_Revoke(cnode_cptr_remaining_untypeds, acpi_ut_idx, 58); */
    /* sddf_dprintf("seL4_CNode_Revoke Error: %d\n", error); */
    free_slot++;

    // TODO: pass PCI resource information here so pages mapped in ACPI driver can be revoked simplpy




    // Print summary
    sddf_dprintf("\n======PCI resources summary:======\n");
    for (int i = 0; i < pci_resources.num_pci_groups; i++) {
        sddf_dprintf("PCI segment group: %u, base addr: 0x%lx, bus_range: [%u-%u]\n",
                     pci_resources.pci_seg_groups[i].group_id,
                     pci_resources.pci_seg_groups[i].base_addr,
                     pci_resources.pci_seg_groups[i].bus_start,
                     pci_resources.pci_seg_groups[i].bus_end);
        uint32_t ecam_size = (1 + pci_resources.pci_seg_groups[i].bus_end - pci_resources.pci_seg_groups[i].bus_start) * (1 << 20);
        uintptr_t end_paddr = pci_resources.pci_seg_groups[i].base_addr + ecam_size;
        uintptr_t cur_paddr = pci_resources.pci_seg_groups[i].base_addr;
        uintptr_t cur_vaddr = 0x5000000;
        while (cur_paddr < end_paddr) {
            uint32_t ut_idx = find_untyped_id_by_paddr(cur_paddr);
            uintptr_t ut_end_paddr = capDLBootInfo->untypedList[ut_idx].paddr + (1 << capDLBootInfo->untypedList[ut_idx].sizeBits);
            sddf_dprintf("Found ut paddr: 0x%lx-0x%lx, cur_paddr: 0x%lx\n", capDLBootInfo->untypedList[ut_idx].paddr, ut_end_paddr, cur_paddr);
            retype_at_offset(cnode_cptr_remaining_untypeds + ut_idx,
                             capDLBootInfo->untypedList[ut_idx].paddr,
                             cnode_cptr_remaining_untypeds,
                             cur_paddr,
                             seL4_X86_LargePageObject,
                             &free_slot);

            sddf_dprintf("try mapping\n");

            free_slot++;
            error = map_frame(cnode_cptr_remaining_untypeds + ut_pt_idx, cnode_cptr_remaining_untypeds + free_slot - 1, vspace_cptr_pci_driver, cur_vaddr, seL4_CanRead, cnode_cptr_remaining_untypeds, &free_slot);
            if (error) {
                sddf_dprintf("map_frame error - %d\n", error);
                return;
            }
            sddf_dprintf("largePage: 0x%x\n", 1 << seL4_LargePageBits);

            free_slot++;
            cur_paddr += (1 << seL4_LargePageBits);
            cur_vaddr += (1 << seL4_LargePageBits);

            while (cur_paddr < end_paddr && cur_paddr < ut_end_paddr) {
                error = seL4_Untyped_Retype(cnode_cptr_remaining_untypeds + ut_idx,
                                            seL4_X86_LargePageObject,
                                            0,
                                            cnode_cptr_remaining_untypeds, 0, 0,
                                            free_slot, 1);
                free_slot++;

                map_frame(cnode_cptr_remaining_untypeds + ut_pt_idx, cnode_cptr_remaining_untypeds + free_slot - 1, vspace_cptr_pci_driver, cur_vaddr, seL4_CanRead, cnode_cptr_remaining_untypeds, &free_slot);
                if (error) {
                    sddf_dprintf("map_frame error - %d\n", error);
                    return;
                }

                cur_paddr += (1 << seL4_LargePageBits);
                cur_vaddr += (1 << seL4_LargePageBits);
            }
        }
    }
    sddf_dprintf("Finished ECAM mapping!\n");

    sddf_deferred_notify(0);

    // TODO: unmap all the pages/frames
    // TODO: revoke all the untypeds used
}

void notified(microkit_channel ch)
{
}
