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


// A system could have up to 65536 PCI Segment Groups in theory, but 16 is
// sufficient in our use cases.
#define MAX_NUM_PCI_SEG_GROUP 16
#define MAX_BYTES_DSDT 10000

uintptr_t remaining_untypeds_vaddr;
typedef struct {
    seL4_CNode untyped_cnode_cptr;
    seL4_SlotRegion untypeds;
    seL4_UntypedDesc untypedList[CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS];
} capDLBootInfo_t;

const char acpi_str_fadt[] = {'F', 'A', 'C', 'P', 0};
const char acpi_str_mcfg[] = {'M', 'C', 'F', 'G', 0};

capDLBootInfo_t *capDLBootInfo;

/* Root System Descriptor Pointer */
typedef struct acpi_rsdp {
    char         signature[8];
    uint8_t      checksum;
    char         oem_id[6];
    uint8_t      revision;
    uint32_t     rsdt_address;
    uint32_t     length;
    uint64_t     xsdt_address;
    uint8_t      extended_checksum;
    char         reserved[3];
} __attribute__((packed)) acpi_rsdp_t;

/* Generic System Descriptor Table Header */
typedef struct acpi_header {
    char         signature[4];
    uint32_t     length;
    uint8_t      revision;
    uint8_t      checksum;
    char         oem_id[6];
    char         oem_table_id[8];
    uint32_t     oem_revision;
    char         creater_id[4];
    uint32_t     creater_revision;
} __attribute__((packed)) acpi_header_t;

/* Root System Descriptor Table */
typedef struct acpi_rsdt {
    acpi_header_t  header;
    uint32_t entry[1];
} __attribute__((packed)) acpi_rsdt_t;

typedef struct acpi_fadt {
    acpi_header_t header;
    uint32_t fw_ctrl;
    uint32_t dsdt;
} __attribute__((packed)) acpi_fadt_t;

typedef struct pci_seg_group {
    uint64_t base_addr;
    uint16_t group_id;
    uint8_t bus_start;
    uint8_t bus_end;
    uint8_t reserved[4];
} __attribute__((packed)) pci_seg_group_t;

typedef struct acpi_mcfg {
    acpi_header_t header;
    uint8_t reserved[8];
    pci_seg_group_t pci_seg_group[MAX_NUM_PCI_SEG_GROUP];
} __attribute__((packed)) acpi_mcfg_t;


typedef struct acpi_dsdt {
    acpi_header_t header;
    uint8_t content[MAX_BYTES_DSDT];
} __attribute__((packed)) acpi_dsdt_t;

typedef struct bootinfo_rsdp {
    seL4_BootInfoHeader header;
    acpi_rsdp_t content;
} __attribute__((packed)) bootinfo_rsdp_t;

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
                pci_seg_group_t *pci_seg_grp = &mcfg_table->pci_seg_group[j];
                microkit_dbg_puts("PCI segment group: ");
                microkit_dbg_put32(pci_seg_grp->group_id);
                microkit_dbg_puts(", base address: ");
                microkit_dbg_put32(pci_seg_grp->base_addr >> 32);
                microkit_dbg_puts(" ");
                microkit_dbg_put32(pci_seg_grp->base_addr & 0xFFFFFFFF);
                microkit_dbg_puts(", bus[");
                microkit_dbg_put32(pci_seg_grp->bus_start);
                microkit_dbg_puts("-");
                microkit_dbg_put32(pci_seg_grp->bus_end);
                microkit_dbg_puts("]\n");
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
    aml_path_seg_t path;
    /* pci_resources_t pci_res; */
    extract_device_resources(&acpi_dsdt_table->content[0], header->length - sizeof(acpi_header_t), &path);
    sddf_dprintf("DSDT has been parsed!\n");

    /* uint8_t *str = (uint8_t *)header; */
    /* for (int i = 0; i < acpi_dsdt_table->header.length; i++) { */
    /*     if (i % 32 == 0) { */
    /*         microkit_dbg_puts("\n"); */
    /*     } */
    /*     microkit_dbg_put8(str[i]); */
    /*     microkit_dbg_puts(" "); */
    /* } */
    /* microkit_dbg_puts("\n"); */


    error = seL4_CNode_Revoke(capDLBootInfo->untyped_cnode_cptr, acpi_ut_idx, 58);
    microkit_dbg_puts("seL4_CNode_Revoke Error: ");
    microkit_dbg_put32(error);
    microkit_dbg_puts("\n=====================\n");

    // TODO: unmap all the pages/frames
    // TODO: revoke all the untypeds used
}

void notified(microkit_channel ch)
{
}
