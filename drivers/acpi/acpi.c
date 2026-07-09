/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <microkit.h>
//#include <types.h>
#include <sel4/bootinfo_types.h>
#include <sel4/sel4_arch/mapping.h>
#include <sel4/sel4_arch/constants.h>
#include <sddf/util/vspace.h>

#include "acpi.h"

uintptr_t remaining_untypeds_vaddr;
typedef struct {
    /* seL4_CNode untyped_cnode_cptr; */
    seL4_SlotRegion untypeds;
    seL4_UntypedDesc untypedList[CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS];
} capDLBootInfo_t;

const char acpi_str_rsdt[] = {'R', 'S', 'D', 'T', 0};
const char acpi_str_dsdt[] = {'D', 'S', 'D', 'T', 0};
const char acpi_str_ssdt[] = {'S', 'S', 'D', 'T', 0};
const char acpi_str_fadt[] = {'F', 'A', 'C', 'P', 0};
const char acpi_str_mcfg[] = {'M', 'C', 'F', 'G', 0};
const char aml_str_hid[] = {'_', 'H', 'I', 'D', 0};  // Hardware ID
const char aml_str_crs[] = {'_', 'C', 'R', 'S', 0};  // Current Resource Settings
const char aml_str_prt[] = {'_', 'P', 'R', 'T', 0};  // PCI Routing Table
const char aml_str_pic[] = {'_', 'P', 'I', 'C', 0};  // PIC mode method
const char eisaid_str_pcie[] = {'P', 'N', 'P', '0', 'A', '0', '8', 0};  // PCI Express Bus

capDLBootInfo_t *capDLBootInfo;
uintptr_t aml_object_pool_start = 0x30000000;
uintptr_t aml_object_pool_size = 0x100000;
pci_resources_t *pci_resources = (pci_resources_t *)0x60000000;
uintptr_t ecam_base_vaddr = 0x20000000;

seL4_CPtr vspace_cptr_pci_driver;
seL4_CPtr cnode_cptr_remaining_untypeds;
seL4_CPtr cnode_cptr_pci_resources;
uintptr_t bootinfo_remaining_untypeds;
uintptr_t bootinfo_rsdp;
seL4_CPtr cnode_pci_resources_free_slot = 1;

uintptr_t acpi_vaddr = 0x4000000;

cnode_specs_t post_boot_cnode;
cnode_specs_t *cnode_caps_pci_resources;

mempool_t aml_namespace_mempool;
aml_namespace_node_t namespace_root;

// Lookup results of AML namespace nodes
#define MAX_NUM_LOOKUP_NODES 128
aml_namespace_node_t *lookup_results[MAX_NUM_LOOKUP_NODES];

__attribute__((__aligned__(0x1000))) __attribute__((__section__(".acpi_tables"))) uint8_t acpi_tables[500000];
__attribute__((__section__(".acpi_tables_summary"))) acpi_tables_summary_t acpi_tables_summary;

void pass_resource_with_range(uint8_t resource_type, uint64_t min_address, uint64_t max_address)
{
    switch (resource_type) {
        case 0: {
            /* pass_ut_with_range(dev_res->min_addr, dev_res->max_addr); */
            break;
            sddf_dprintf("Memory ");
        }
        case 1: {
            sddf_dprintf("IO ");
            break;
        }
        case 2: {
            sddf_dprintf("Bus ");
            break;
        }
    }
    sddf_dprintf(": [0x%lx-0x%lx]\n", min_address, max_address);
}

// Section 6.4
void pass_crs_and_caps(aml_data_t crs_data, uint32_t bridge_idx)
{
    uint8_t *buf_cur = (uint8_t *)crs_data.value;
    uint8_t *crs_data_end = (uint8_t *)crs_data.value + crs_data.length;

    // TODO: deal with WORD_IO and WORD_BUS
    sddf_dprintf("=====pass CRS untypeds=====\n");
    while (buf_cur < crs_data_end) {
        uint8_t new_res_idx = pci_resources->bridges[bridge_idx].num_dev_resources;
        device_resource_t *dev_res = (device_resource_t *)&pci_resources->bridges[bridge_idx].dev_resources[new_res_idx];

        switch (buf_cur[0]) {
            case WORD_AS_DESCRIPTOR: {
                acpi_word_address_space_t *word_as = (acpi_word_address_space_t *)buf_cur;
                dev_res->min_addr = word_as->min_address;
                dev_res->max_addr = word_as->min_address + word_as->address_length;
                dev_res->type = word_as->resource_type;

                sddf_dprintf("Word ");
                pass_resource_with_range(dev_res->type, dev_res->min_addr, dev_res->max_addr);

                pci_resources->bridges[bridge_idx].num_dev_resources++;
                break;
            }
            case DWORD_AS_DESCRIPTOR: {
                acpi_dword_address_space_t *dword_as = (acpi_dword_address_space_t *)buf_cur;
                dev_res->min_addr = dword_as->min_address;
                dev_res->max_addr = dword_as->min_address + dword_as->address_length;
                dev_res->type = dword_as->resource_type;

                sddf_dprintf("DWord ");
                pass_resource_with_range(dev_res->type, dev_res->min_addr, dev_res->max_addr);

                pci_resources->bridges[bridge_idx].num_dev_resources++;
                break;
            }
            case QWORD_AS_DESCRIPTOR: {
                acpi_qword_address_space_t *qword_as = (acpi_qword_address_space_t *)buf_cur;
                dev_res->min_addr = qword_as->min_address;
                dev_res->max_addr = qword_as->min_address + qword_as->address_length;
                dev_res->type = qword_as->resource_type;

                sddf_dprintf("QWord ");
                pass_resource_with_range(dev_res->type, dev_res->min_addr, dev_res->max_addr);

                pci_resources->bridges[bridge_idx].num_dev_resources++;
                break;
            }
            case IO_PORT_DESCRIPTOR: {
                acpi_io_port_t *io_port = (acpi_io_port_t *)buf_cur;
                dev_res->min_addr = io_port->min_address;
                dev_res->max_addr = io_port->min_address + io_port->address_length;

                sddf_dprintf("I/O Port ");
                pass_resource_with_range(1, dev_res->min_addr, dev_res->max_addr);
                break;
            }
            case END_TAG: {
                sddf_dprintf("end_tag\n");
                // TODO: checksum
                break;
            }
            default: {
                sddf_dprintf("Resource type 0x%02x parsing is not implemented\n", buf_cur[0]);
            }
        }

        if (buf_cur[0] & 0x80) {
            // Large Resource Data Length
            buf_cur += 3 + buf_cur[1] + (buf_cur[2] << 8);
        } else {
            // Small Resource Data Length: Byte0[2:0]
            buf_cur += (buf_cur[0] & 0x7) + 1;
        }
    }
}

// TODO: this should be in interpreter.c

bool validate_acpi_table_signature(acpi_header_t *header, const char *signature)
{
    sddf_dprintf("Signature: %c%c%c%c\n",
                 header->signature[0],
                 header->signature[1],
                 header->signature[2],
                 header->signature[3]);

    assert(header->signature[0] == signature[0]);
    assert(header->signature[1] == signature[1]);
    assert(header->signature[2] == signature[2]);
    assert(header->signature[3] == signature[3]);
    return true;
}

bool map_acpi_table_header(uintptr_t paddr, acpi_header_t *header)
{
    return map_memory_region(&post_boot_cnode, paddr, sizeof(acpi_header_t), (uintptr_t)header);
}

bool map_acpi_table_content(uintptr_t paddr, acpi_header_t *header)
{
    uintptr_t mapped_paddr_end = ROUND_UP(paddr + sizeof(acpi_header_t), PAGE_SIZE);
    uintptr_t mapped_vaddr_end = ROUND_UP((uintptr_t)header + sizeof(acpi_header_t), PAGE_SIZE);
    uintptr_t acpi_table_paddr_end = paddr + header->length;
    return map_memory_region(&post_boot_cnode, mapped_paddr_end, acpi_table_paddr_end - mapped_paddr_end, mapped_vaddr_end);
}

void backup_acpi_table(acpi_header_t *header)
{
    uintptr_t backup_table_vaddr = ROUND_UP((uintptr_t)&acpi_tables + acpi_tables_summary.tables_end, ACPI_TABLES_ALIGNMENT);
    sddf_dprintf("backup_table_vaddr: 0x%lx, len: 0x%x, end: 0x%lx\n", backup_table_vaddr, header->length, backup_table_vaddr + header->length);
    assert(backup_table_vaddr + header->length < acpi_tables_summary.mem_end);
    memcpy((void *)backup_table_vaddr, (void *)header, header->length);

    uint32_t table_idx = acpi_tables_summary.num_tables;
    acpi_tables_summary.tables[table_idx] = (acpi_header_t *)backup_table_vaddr;
    acpi_tables_summary.num_tables++;
    acpi_tables_summary.tables_end = backup_table_vaddr + header->length - (uintptr_t)&acpi_tables;
    sddf_dprintf("update tables_end to 0x%lx\n", acpi_tables_summary.tables_end);
}

acpi_header_t *find_first_acpi_header_by_signature(const char *signature)
{
    for (int i = 0; i < acpi_tables_summary.num_tables; i++) {
        acpi_header_t *header = acpi_tables_summary.tables[i];
        if (strncmp(header->signature, signature, 4) == 0) {
            return header;
        }
    }
    return NULL;
}

void load_acpi_tables()
{
    // Read RSDP to locate RSDT
    bootinfo_rsdp_t *bi_rsdp = (bootinfo_rsdp_t *)bootinfo_rsdp;
    sddf_dprintf("revision: %d, rsdt_addr: 0x%x, xsdt_addr: 0x%lx\n",
                 bi_rsdp->content.revision,
                 bi_rsdp->content.rsdt_address,
                 bi_rsdp->content.xsdt_address);
    uintptr_t rsdt_paddr = bi_rsdp->content.rsdt_address;
    if (bi_rsdp->content.revision > 1) {
        rsdt_paddr = bi_rsdp->content.xsdt_address;
    }

    // Map all the frames covering the RSDT table
    acpi_header_t *rsdt_header = (acpi_header_t *)(acpi_vaddr + PAGE_OFFSET(rsdt_paddr));
    assert(map_acpi_table_header(rsdt_paddr, rsdt_header));
    validate_acpi_table_signature(rsdt_header, acpi_str_rsdt);

    assert(map_acpi_table_content(rsdt_paddr, rsdt_header));
    backup_acpi_table(rsdt_header);
    assert(cnode_untypeds_revoke(&post_boot_cnode) == seL4_NoError);

    acpi_header_t *acpi_rsdt_header = find_first_acpi_header_by_signature(acpi_str_rsdt);
    assert(acpi_rsdt_header != NULL);

    acpi_rsdt_t *acpi_rsdt = (acpi_rsdt_t *)acpi_rsdt_header;
    // TODO: XSDT has different struct size
    uint32_t num_entries = (acpi_rsdt->header.length - sizeof(acpi_rsdt->header)) / sizeof(uint32_t);
    sddf_dprintf("rsdt: 0x%lx, entries: %d, length: %d\n", (uintptr_t)acpi_rsdt_header, num_entries, acpi_rsdt->header.length);
    uint32_t *table_entries = (uint32_t *)&acpi_rsdt->entry;

    // Look up entries in RSDT
    for (int i = 0; i < num_entries; i++) {
        acpi_header_t *header = (acpi_header_t *)(acpi_vaddr + (table_entries[i] & 0xfff));
        assert(map_acpi_table_header(table_entries[i], header));

        sddf_dprintf("Signature: %c%c%c%c\n",
                 header->signature[0],
                 header->signature[1],
                 header->signature[2],
                 header->signature[3]);
        sddf_dprintf("Entry pointer: 0x%lx, location: 0x%lx\n", table_entries[i], &table_entries[i]);

        if (strncmp(header->signature, acpi_str_fadt, 4) == 0) {
            assert(map_acpi_table_content(table_entries[i], header));

            acpi_fadt_t *fadt_table = (acpi_fadt_t *)header;
            sddf_dprintf("DSDT address: 0x%x\n", fadt_table->dsdt);
            uintptr_t acpi_dsdt_paddr = fadt_table->dsdt;

            assert(cnode_untypeds_revoke(&post_boot_cnode) == seL4_NoError);
            // FADT table has been unmapped, so it's no longer readable

            acpi_header_t *dsdt_header = (acpi_header_t *)(acpi_vaddr + (acpi_dsdt_paddr & 0xfff));
            assert(map_acpi_table_header(acpi_dsdt_paddr, dsdt_header));
            validate_acpi_table_signature(dsdt_header, acpi_str_dsdt);

            // Map and backup the DSDT table
            assert(map_acpi_table_content(acpi_dsdt_paddr, dsdt_header));
            backup_acpi_table(dsdt_header);

        } else if (strncmp(header->signature, acpi_str_mcfg, 4) == 0) {
            // Map and backup the MCFG table
            assert(map_acpi_table_content(table_entries[i], header));
            backup_acpi_table(header);

        } else if (strncmp(header->signature, acpi_str_ssdt, 4) == 0) {
            // Map and backup the SSDT table
            assert(map_acpi_table_content(table_entries[i], header));
            backup_acpi_table(header);
        }

        assert(cnode_untypeds_revoke(&post_boot_cnode) == seL4_NoError);
    }
}

void init(void)
{
    // Init the CNode specs that record all the untypeds passed from the capDL initialiser
    capDLBootInfo = (capDLBootInfo_t*)bootinfo_remaining_untypeds;
    post_boot_cnode.cptr = cnode_cptr_remaining_untypeds;
    post_boot_cnode.start = capDLBootInfo->untypeds.start;
    // TODO: is end empty?
    for (uint64_t i = capDLBootInfo->untypeds.start; i < capDLBootInfo->untypeds.end; i++) {
        post_boot_cnode.caps[i].base_addr = capDLBootInfo->untypedList[i].paddr;
        post_boot_cnode.caps[i].end_addr = post_boot_cnode.caps[i].base_addr + (1ULL << capDLBootInfo->untypedList[i].sizeBits);
        post_boot_cnode.caps[i].is_device = capDLBootInfo->untypedList[i].isDevice;
        post_boot_cnode.caps[i].object_type = seL4_UntypedObject;
        post_boot_cnode.end = i + 1;
    }
    update_active_ut_idx(&post_boot_cnode);

    sddf_dprintf("ACPI tables summary:\n");
    sddf_dprintf("  num_tables: %d\n", acpi_tables_summary.num_tables);
    sddf_dprintf("  mem_size: %d\n", acpi_tables_summary.mem_end);
    sddf_dprintf("  tables_end: %d\n", acpi_tables_summary.tables_end);

    if (acpi_tables_summary.num_tables == 0) {
        load_acpi_tables();
    }

    sddf_dprintf("======MAP ======\n");

    acpi_mcfg_t *mcfg_table = (acpi_mcfg_t *)find_first_acpi_header_by_signature(acpi_str_mcfg);
    assert(mcfg_table != NULL);

    uint32_t num_pci_seg_grps = (mcfg_table->header.length - sizeof(acpi_header_t)) / sizeof(pci_seg_group_t);
    sddf_dprintf("num_pci: %u\n", num_pci_seg_grps);
    for (int i = 0; i < num_pci_seg_grps; i++) {
        void *src_table = (void *)&mcfg_table->pci_seg_group[i];
        void *dst_table = (void *)&pci_resources->pci_seg_groups[pci_resources->num_pci_groups];
        memcpy(dst_table, src_table, sizeof(pci_seg_group_t));
        pci_resources->num_pci_groups++;
    }

    sddf_dprintf("===============Scanning DSDT and SSDT===============\n");
    aml_namespace_mempool.start = (void *)aml_object_pool_start;
    aml_namespace_mempool.next = (void *)aml_object_pool_start;
    aml_namespace_mempool.end = (void *)aml_object_pool_start + aml_object_pool_size;

    acpi_dsdt_t *dsdt_table = (acpi_dsdt_t *)find_first_acpi_header_by_signature(acpi_str_dsdt);
    assert(dsdt_table != NULL);
    uint8_t *dsdt_table_end = (uint8_t *)dsdt_table + dsdt_table->header.length;
    set_scanner_to((uint8_t *)&dsdt_table->content[0]);
    namespace_root.pkt_start = scanner.current;
    namespace_root.op_code = NULL_OP;
    namespace_root.name[0] = '\\';
    scan_namespace_tree(&namespace_root, dsdt_table_end);

    for (int i = 0; i < acpi_tables_summary.num_tables; i++) {
        if (strncmp(acpi_tables_summary.tables[i]->signature, acpi_str_ssdt, 4) == 0) {
            acpi_dsdt_t *ssdt_table = (acpi_dsdt_t *)acpi_tables_summary.tables[i];
            uint8_t *ssdt_table_end = (uint8_t *)ssdt_table + ssdt_table->header.length;
            set_scanner_to((uint8_t *)&ssdt_table->content[0]);
            scan_namespace_tree(&namespace_root, ssdt_table_end);
        }
    }

    // Look for _PIC method
    uint8_t num_results = find_decendant_nodes_by_name(&namespace_root, aml_str_pic, lookup_results, 0);
    assert(num_results == 1 && num_results < MAX_NUM_LOOKUP_NODES); // There must be only one _PIC method
    sddf_dprintf("Found _PIC method! num: %u\n", num_results);

    // Enable APIC mode: pass 1 to method "_PIC"
    aml_data_t pic_method_arg = {1, DATA_OBJ_QWORD, 0};
    // TODO: fix ret_type
    eval_namespace_node(lookup_results[0], 1, &pic_method_arg);

    // Extract _CRS and _PRT
    sddf_dprintf("===============Extract _CRS===============\n");
    num_results = find_decendant_nodes_by_name(&namespace_root, aml_str_hid, lookup_results, 0);
    assert(num_results == num_pci_seg_grps); // Num of PCIe bridges should be matched in MCFG and DSDT

    for (uint32_t i = 0; i < num_results; i++) {
        aml_namespace_node_t *node = lookup_results[i];
        char eisa_id[10];
        read_eisa_id(node, eisa_id);
        if (!strcmp(eisa_id, eisaid_str_pcie)) {
            sddf_dprintf("=====Found PCIe Bus\n");
            aml_namespace_node_t *crs_node = find_child_node_by_name(node->parent, aml_str_crs);
            assert(crs_node != NULL);

            /* aml_data_t crs_data_before_eval = {0x21675b, 17, 540}; */
            /* pass_crs_and_caps(crs_data_before_eval, pci_resources->num_bridges); */
            // TODO: fix ret_type
            aml_data_t crs_data = eval_namespace_node(crs_node, 0, NULL);
            pass_crs_and_caps(crs_data, pci_resources->num_bridges);
            sddf_dprintf("======Finish _CRS parsing\n");

            aml_namespace_node_t *prt_node = find_child_node_by_name(node->parent, aml_str_prt);
            assert(prt_node != NULL);

            aml_data_t prt_data = eval_namespace_node(prt_node, 0, NULL);
            sddf_dprintf("value: 0x%lx, type: %u, length: %u\n", prt_data.value, prt_data.type, prt_data.length);
            parse_prt_package(prt_data, pci_resources->num_bridges);
            pci_resources->num_bridges++;
            sddf_dprintf("======Finish _PRT parsing\n");
        }
    }

    // Map ECAM space for PCIe driver
    seL4_Error error;
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
            error = retype_and_map_frame(&post_boot_cnode, cur_paddr, cur_vaddr, seL4_CapInitThreadVSpace, seL4_X86_LargePageObject, seL4_ReadWrite);
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


    sddf_deferred_notify(0);
}

void notified(microkit_channel ch)
{
}
