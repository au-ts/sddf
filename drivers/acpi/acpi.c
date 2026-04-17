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

#include "acpi.h"


uintptr_t remaining_untypeds_vaddr;
typedef struct {
    seL4_CNode untyped_cnode_cptr;
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
scanner_t scanner;
aml_object_pool_t object_pool;
aml_object_t object_root;
pci_resources_t pci_resources;
aml_object_t *lookup_results[50];
uint32_t lookup_cnt;

void print_64(seL4_Word w) {
    microkit_dbg_put32((seL4_Uint32) (w >> 32));
    microkit_dbg_put32((seL4_Uint32) w);
}

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
                            seL4_CPtr *free_slots)
{
    seL4_Error error;
    seL4_Word current_paddr = parent_paddr;
    seL4_Word remaining_offset = target_paddr - parent_paddr;

    // 1. Divide preceding memory into smaller Untypeds
    // We iterate from 30 (1GB) down to 12 (4KB)
    for (int bits = 30; bits >= 12; bits--) {
        seL4_Word size = (1UL << bits);

        while (remaining_offset >= size) {
            // Create a "filler" Untyped to move the allocation pointer forward
            microkit_dbg_puts("retype ");
            microkit_dbg_put32(bits);
            microkit_dbg_puts("\n");
            error = seL4_Untyped_Retype(parent_untyped,
                                        seL4_UntypedObject,
                                        bits,
                                        cnode_cptr, 0, 0,
                                        *free_slots, 1);
            if (error != seL4_NoError) return error;

            (*free_slots)++; // Use next slot
            remaining_offset -= size;
            current_paddr += size;
            microkit_dbg_puts("create untyped size ");
            microkit_dbg_put32(bits);
            microkit_dbg_puts(" at ");
            microkit_dbg_put32(current_paddr - size);
            microkit_dbg_puts("\n");
        }
    }

    // 2. Now the parent Untyped's internal pointer is at target_paddr
    // Retype the actual Frame
    error = seL4_Untyped_Retype(parent_untyped,
                                seL4_X86_4K, // Or seL4_ARM_SmallPageObject
                                0,
                                cnode_cptr, 0, 0,
                                *free_slots, 1);

    if (error == seL4_NoError) {
        microkit_dbg_puts("create frame at ");
        microkit_dbg_put32(current_paddr);
        microkit_dbg_puts("\n");
      /* printf("Success! Frame created at target 0x%lx in slot %ld\n", target_paddr, *free_slots); */
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

void init(void)
{
    // TODO: probably should use Bill's patch for prefilling memory regions
    // TODO: extract RSDT according to revision
    bootinfo_rsdp_t *bi_rsdp = (bootinfo_rsdp_t *)0x3000000;
    microkit_dbg_puts("\nrevision: ");
    microkit_dbg_put32(bi_rsdp->content.revision);
    microkit_dbg_puts("\nrsdt: ");
    microkit_dbg_put32(bi_rsdp->content.rsdt_address);
    microkit_dbg_puts("\nxsdt: ");
    microkit_dbg_put32(bi_rsdp->content.xsdt_address);
    microkit_dbg_puts("\n");
    uintptr_t rsdt_addr = bi_rsdp->content.rsdt_address;


    microkit_dbg_puts("size of capDLBootInfo_t: ");
    microkit_dbg_put32(sizeof(capDLBootInfo_t));
    microkit_dbg_puts("\nMAX_NUM_UNTYPEDS: ");
    microkit_dbg_put32(CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS);
    microkit_dbg_puts("\n");

    capDLBootInfo = (capDLBootInfo_t*) remaining_untypeds_vaddr;
    microkit_dbg_puts("untyped_cnode_cptr: ");
    microkit_dbg_put32((seL4_Uint32) (capDLBootInfo->untyped_cnode_cptr >> 32));
    microkit_dbg_putc(32);
    microkit_dbg_put32((seL4_Uint32) capDLBootInfo->untyped_cnode_cptr);
    microkit_dbg_puts("\n");

    uint32_t ut_pt_idx = 0;
    bool second_non_dev_mem = false;

    for (uint32_t i = capDLBootInfo->untypeds.start; i < capDLBootInfo->untypeds.end; i++) {
        if (!capDLBootInfo->untypedList[i].isDevice) {
            // TODO: find a proper untyped for PT objects, not the first one is used by capDL initialiser
            if (second_non_dev_mem) {
                ut_pt_idx = i;
                break;
            }
            second_non_dev_mem = true;
        }
    }
    microkit_dbg_puts("untyped idx: ");
    microkit_dbg_put32(ut_pt_idx);
    microkit_dbg_puts("\n");

    uint32_t acpi_ut_idx = find_untyped_id_by_paddr(rsdt_addr);
    microkit_dbg_puts("acpi ut idx: ");
    microkit_dbg_put32(acpi_ut_idx);
    microkit_dbg_puts("\n");

    map_pts(capDLBootInfo->untyped_cnode_cptr + ut_pt_idx, capDLBootInfo->untyped_cnode_cptr, capDLBootInfo->untypeds.end);

    seL4_CPtr free_slot = capDLBootInfo->untypeds.end + frame + 1;
    retype_at_offset(capDLBootInfo->untyped_cnode_cptr + acpi_ut_idx,
                     capDLBootInfo->untypedList[acpi_ut_idx].paddr,
                     capDLBootInfo->untyped_cnode_cptr,
                     rsdt_addr, &free_slot);

    seL4_Error error = seL4_X86_Page_Map(capDLBootInfo->untyped_cnode_cptr + free_slot, seL4_CapInitThreadVSpace, acpi_vaddr,
                              seL4_CanRead,
                              seL4_X86_Default_VMAttributes);

    if (error != seL4_NoError) {
        microkit_dbg_puts("Failed to map frame\n");
    }

    uint32_t rsdt_offset = rsdt_addr & 0xFFF;
    volatile acpi_rsdt_t *acpi_rsdt = (acpi_rsdt_t *)(acpi_vaddr + rsdt_offset);

    // TODO: validate
    microkit_dbg_puts("RSDT signature: ");
    microkit_dbg_putc(acpi_rsdt->header.signature[0]);
    microkit_dbg_putc(acpi_rsdt->header.signature[1]);
    microkit_dbg_putc(acpi_rsdt->header.signature[2]);
    microkit_dbg_putc(acpi_rsdt->header.signature[3]);
    microkit_dbg_puts("\n");

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

        microkit_dbg_puts("map ");
        microkit_dbg_put32(i);
        microkit_dbg_puts("th page\n");
        retype_at_offset(capDLBootInfo->untyped_cnode_cptr + following_acpi_ut_idx,
                         acpi_ut_paddr,
                         capDLBootInfo->untyped_cnode_cptr,
                         rsdt_addr + i * 4096, &free_slot);

        seL4_X86_Page_Map(capDLBootInfo->untyped_cnode_cptr + free_slot,
                          seL4_CapInitThreadVSpace,
                          acpi_vaddr + i * 4096,
                          seL4_CanRead,
                          seL4_X86_Default_VMAttributes);
    }

    // TODO: XSDT has different struct size
    uint32_t entries = (acpi_rsdt->header.length - sizeof(acpi_rsdt->header)) / sizeof(uint32_t);
    microkit_dbg_puts("entries: ");
    microkit_dbg_put32(entries);
    microkit_dbg_puts("\n");

    microkit_dbg_puts("offset: ");
    microkit_dbg_put32(rsdt_offset);
    microkit_dbg_puts("\n");

    microkit_dbg_puts("length: ");
    microkit_dbg_put32(acpi_rsdt->header.length);
    microkit_dbg_puts("\n");

    for (int i = 0; i < entries; i++) {
        acpi_rsdt_entries[i] = acpi_rsdt->entry[i];
        /* microkit_dbg_put32(acpi_rsdt->entry[i]); */
        /* microkit_dbg_puts("\n"); */
    }

    // depth = guard_size(50) + size_bits(8)
    error = seL4_CNode_Revoke(capDLBootInfo->untyped_cnode_cptr, acpi_ut_idx, 58);
    microkit_dbg_puts("Error: ");
    microkit_dbg_put32(error);
    microkit_dbg_puts("\n");

    free_slot = capDLBootInfo->untypeds.end + frame + 1;

    for (int i = 0; i < entries; i++) {
        acpi_ut_idx = find_untyped_id_by_paddr(acpi_rsdt_entries[i]);
        retype_at_offset(capDLBootInfo->untyped_cnode_cptr + acpi_ut_idx,
                         capDLBootInfo->untypedList[acpi_ut_idx].paddr,
                         capDLBootInfo->untyped_cnode_cptr,
                         acpi_rsdt_entries[i], &free_slot);

        error = seL4_X86_Page_Map(capDLBootInfo->untyped_cnode_cptr + free_slot, seL4_CapInitThreadVSpace, acpi_vaddr,
                              seL4_CanRead,
                              seL4_X86_Default_VMAttributes);

        acpi_header_t *header = (acpi_header_t *)(acpi_vaddr + (acpi_rsdt_entries[i] & 0xfff));

        microkit_dbg_put32(acpi_rsdt_entries[i]);
        microkit_dbg_puts("\n");
        microkit_dbg_puts("Table signature: ");
        microkit_dbg_putc(header->signature[0]);
        microkit_dbg_putc(header->signature[1]);
        microkit_dbg_putc(header->signature[2]);
        microkit_dbg_putc(header->signature[3]);
        microkit_dbg_puts("\nlength: ");
        microkit_dbg_put32(header->length);
        microkit_dbg_puts("\n");
        if (strncmp(header->signature, acpi_str_fadt, 4) == 0) {
            microkit_dbg_puts("Found FADT table!\n");
            acpi_fadt_t *fadt_table = (acpi_fadt_t *)header;
            microkit_dbg_puts("DSDT address: ");
            microkit_dbg_put32(fadt_table->dsdt);
            microkit_dbg_puts("\n");
            acpi_dsdt_addr = fadt_table->dsdt;
        } else if (strncmp(header->signature, acpi_str_mcfg, 4) == 0) {
            microkit_dbg_puts("Found MCFG table!\n");

            acpi_mcfg_t *mcfg_table = (acpi_mcfg_t *)header;
            uint32_t num_pci_seg_grps = (mcfg_table->header.length - sizeof(acpi_header_t)) / sizeof(pci_seg_group_t);
            for (int j = 0; j < num_pci_seg_grps; j++) {
                memcpy(&pci_resources.pci_seg_groups[pci_resources.num_pci_groups], &mcfg_table->pci_seg_group[j], sizeof(pci_seg_group_t));
                pci_resources.num_pci_groups++;
            }

        }

        error = seL4_CNode_Revoke(capDLBootInfo->untyped_cnode_cptr, acpi_ut_idx, 58);
        microkit_dbg_puts("Error: ");
        microkit_dbg_put32(error);
        microkit_dbg_puts("\n=====================\n");
    }


    free_slot = capDLBootInfo->untypeds.end + frame + 1;
    // Parse DSDT table
    acpi_ut_idx = find_untyped_id_by_paddr(acpi_dsdt_addr);
    retype_at_offset(capDLBootInfo->untyped_cnode_cptr + acpi_ut_idx,
                     capDLBootInfo->untypedList[acpi_ut_idx].paddr,
                     capDLBootInfo->untyped_cnode_cptr,
                     acpi_dsdt_addr, &free_slot);

    error = seL4_X86_Page_Map(capDLBootInfo->untyped_cnode_cptr + free_slot, seL4_CapInitThreadVSpace, acpi_vaddr,
                          seL4_CanRead,
                          seL4_X86_Default_VMAttributes);

    uint32_t dsdt_offset = acpi_dsdt_addr & 0xfff;
    acpi_header_t *header = (acpi_header_t *)(acpi_vaddr + dsdt_offset);
    microkit_dbg_puts("Table signature: ");
    microkit_dbg_putc(header->signature[0]);
    microkit_dbg_putc(header->signature[1]);
    microkit_dbg_putc(header->signature[2]);
    microkit_dbg_putc(header->signature[3]);
    microkit_dbg_puts("\nlength: ");
    microkit_dbg_put32(header->length);
    microkit_dbg_puts("\n");

    // Map all the frames covering the DSDT table
    for (int i = 1; i * 4096 < dsdt_offset + header->length; i++) {
        uint32_t following_acpi_ut_idx = find_untyped_id_by_paddr(acpi_dsdt_addr + i * 4096);
        free_slot++;

        if (following_acpi_ut_idx == acpi_ut_idx) {
            acpi_ut_paddr =  acpi_dsdt_addr + i * 4096;
        } else {
            acpi_ut_paddr = capDLBootInfo->untypedList[following_acpi_ut_idx].paddr;
        }

        microkit_dbg_puts("map ");
        microkit_dbg_put32(i);
        microkit_dbg_puts("th page\n");
        microkit_dbg_puts("paddr: ");
        microkit_dbg_put32(acpi_dsdt_addr + i * 4096);
        microkit_dbg_puts(" , ut_paddr: ");
        microkit_dbg_put32(acpi_ut_paddr);
        microkit_dbg_puts("\n");
        retype_at_offset(capDLBootInfo->untyped_cnode_cptr + following_acpi_ut_idx,
                         acpi_ut_paddr,
                         capDLBootInfo->untyped_cnode_cptr,
                         acpi_dsdt_addr + i * 4096, &free_slot);

        seL4_X86_Page_Map(capDLBootInfo->untyped_cnode_cptr + free_slot,
                          seL4_CapInitThreadVSpace,
                          acpi_vaddr + i * 4096,
                          seL4_CanRead,
                          seL4_X86_Default_VMAttributes);
    }

    acpi_dsdt_t *acpi_dsdt_table = (acpi_dsdt_t *)header;
    /* /\* aml_path_seg_t path; *\/ */
    /* char path_name[AML_MAX_PATH_STR] = { '\0' }; */
    /* extract_device_resources(&acpi_dsdt_table->content[0], header->length - sizeof(acpi_header_t), path_name, 0); */
    /* sddf_dprintf("DSDT has been parsed!\n"); */

    /* error = seL4_CNode_Revoke(capDLBootInfo->untyped_cnode_cptr, acpi_ut_idx, 58); */
    /* sddf_dprintf("seL4_CNode_Revoke Error: %d\n", error); */

    /* // Map pages for PCI driver */
    /* for (int i = 0; i < pci_resources.num_pci_groups; i++) { */
    /*     // Each PCI bus needs 1M on ECAM, and each segment group has up to 256 buses */
    /*     uint32_t ecam_size = (1 + pci_resources.pci_seg_groups[i].bus_end - pci_resources.pci_seg_groups[i].bus_start) * (1 << 20); */
    /*     sddf_dprintf("base addr: 0x%lx, size: 0x%x\n", pci_resources.pci_seg_groups[i].base_addr, ecam_size); */
    /* } */


    /* // Print summary */
    /* sddf_dprintf("\n======PCI resources summary:======\n"); */
    /* for (int j = 0; j < pci_resources.num_pci_groups; j++) { */
    /*     sddf_dprintf("PCI segment group: %u, base addr: 0x%lx, bus_range: [%u-%u]\n", */
    /*                  pci_resources.pci_seg_groups[j].group_id, */
    /*                  pci_resources.pci_seg_groups[j].base_addr, */
    /*                  pci_resources.pci_seg_groups[j].bus_start, */
    /*                  pci_resources.pci_seg_groups[j].bus_end); */
    /* } */

    sddf_dprintf("===============Scanning DSDT===============\n");

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
    for (uint32_t i = 0; i < lookup_cnt; i++) {
        aml_object_t *node = lookup_results[i];
        sddf_dprintf("i: %u, OpCode: 0x%02X, Name: %s, Location: 0x%lx\n", i, node->op_code, node->name, (uintptr_t)node->start);
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

    // TODO: unmap all the pages/frames
    // TODO: revoke all the untypeds used
}

void notified(microkit_channel ch)
{
}
