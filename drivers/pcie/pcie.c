/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <string.h>
#include <microkit.h>
#include <os/sddf.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>

#include "pcie.h"

__attribute__((__section__(".pcie_config"))) pcie_driver_config_t config;

void *rsdp_dump()
{
    for (char *addr = (char *)BIOS_AREA_START; addr < (char *)BIOS_AREA_END; addr += 16) {
        if (!strncmp(addr, "RSD PTR ", 8)) {
            sddf_dprintf("Found the identifier at 0x%lx:\n", (uintptr_t)addr);
            sddf_dprintf("%c%c%c%c%c%c%c%c\n", addr[0], addr[1], addr[2], addr[3], addr[4], addr[5], addr[6], addr[7]);

            // TODO: validate the checksum
            // TODO: return rsdt_addr
            acpi_rsdp_t *acpi_rsdp = (acpi_rsdp_t *)addr;
            sddf_dprintf("revision: 0x%x\n", acpi_rsdp->revision);
            sddf_dprintf("checksum: 0x%x\n", acpi_rsdp->checksum);
            sddf_dprintf("rsdt: 0x%x\n", acpi_rsdp->rsdt_addr);
            sddf_dprintf("length: 0x%x\n", acpi_rsdp->length);
            sddf_dprintf("xsdt: 0x%lx\n", acpi_rsdp->xsdt_addr);

            // TODO: distinguish ACPI 1.0 and 2.0

            uint32_t checksum = 0;
            for (char *ch = addr; ch < addr + 20; ch++) {
                checksum += (uint8_t)(*ch);
            }
            if ((checksum & 0xFF) != 0) {
                sddf_dprintf("Wrong checksum!\n");
                return NULL;
            }

            return (void *)(uintptr_t)acpi_rsdp->rsdt_addr;
        }
    }

    // No RSDP found!
    return NULL;
}

void *find_sdt(void *rsdt_addr, char *signature)
{
    acpi_sdt_header_t *rsdt_header = (acpi_sdt_header_t *)rsdt_addr;
    int num_entries = (rsdt_header->length - sizeof(acpi_sdt_header_t)) / 4;
    sddf_dprintf("num of entries: 0x%x\n", num_entries);

    for (int i = 0; i < num_entries; i++)
    {
        uint32_t *sdt_pointer = (uint32_t *)((uintptr_t)rsdt_header + sizeof(acpi_sdt_header_t) + 4 * i);
        acpi_sdt_header_t *header = (acpi_sdt_header_t *)(uintptr_t)(*sdt_pointer);
        sddf_dprintf("scan at 0x%lx: %c%c%c%c\n", (uintptr_t)header, header->signature[0], header->signature[1],
                     header->signature[2], header->signature[3]);
        if (!strncmp(header->signature, signature, 4)) {
            sddf_dprintf("MCFG header found at: 0x%lx\n", (uintptr_t)header);
            return (void *)header;
        }
    }

    // No MCFG found
    return NULL;
}

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

void pci_bus_scan(uintptr_t pci_bus)
{
    for (int i = 0; i < 32; i++) {
        for (int k = 0; k < 8; k++) {
            struct pci_config_space *pci_header = (struct pci_config_space *)(pci_bus + (i << 15) + (k << 12));
            if (pci_header->vendor_id != 0xffff && pci_header->vendor_id != 0x0000) {
                sddf_dprintf("bus: 0x%lx, dev: 0x%lx, func: 0x%lx, vedor_id: 0x%x, device_id: 0x%x\n",
                             (((uintptr_t)pci_header >> 20) & 0xff),
                             (((uintptr_t)pci_header >> 15) & 0x1f),
                             (((uintptr_t)pci_header >> 12) & 0x7),
                             pci_header->vendor_id,
                             pci_header->device_id);

                for (int j = 0; j < 64; j++) {
                    if (j && j % 16 == 0) sddf_dprintf("\n");
                    sddf_dprintf("%02x ", *(uint8_t *)(pci_bus + (i << 15) + (k << 12) + j));
                }
                sddf_dprintf("\n");

                if (pci_header->vendor_id == 0x1af4 && pci_header->device_id == 0x1001) {
                    volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x14);
                    sddf_dprintf("Memory BAR 1: 0x%x\n", *mem_bar);
                    /* *mem_bar = 0xFFFFFFFF; */
                    sddf_dprintf("Memory BAR 1: 0x%x\n", *mem_bar);
                    /* *mem_bar = 0xFEBD6000; */
                    sddf_dprintf("Memory BAR 1: 0x%x\n", *mem_bar);


                    struct msix_capability *msix_cap = (struct msix_capability *)find_pci_cap_by_id(pci_header, PCI_CAP_ID_MSIX);
                    if (msix_cap) {
                        // Disable legacy Interrupts
                        pci_header->command = pci_header->command | (1 << 10);

                        uint16_t *test = (uint16_t *)((void *)pci_header + 0x98 + 2);
                        sddf_dprintf("test: 0x%x\n", *test);
                        // Enable MSI-X
                        struct msix_msg_ctrl *msg_ctrl = &msix_cap->msg_ctrl;
                        msg_ctrl->msix_enable = 1;
                        sddf_dprintf("Table Size: 0x%x\n", msg_ctrl->table_size + 1);
                        sddf_dprintf("Function Mask: 0x%x\n", msg_ctrl->func_mask);
                        sddf_dprintf("MSI-X Enable: 0x%x\n", msg_ctrl->msix_enable);

                        struct msix_table *msix_table = (struct msix_table *)0xFEBD5000;
                        msix_table->msg_addr_low = 0xFEEu << 20;
                        msix_table->msg_data = 0x4031;
                        msix_table->vec_ctrl = 0x0;
                        sddf_dprintf("Vector 0 Message Addr Low: 0x%x\n", msix_table->msg_addr_low);
                        sddf_dprintf("Vector 0 Message Addr Hi: 0x%x\n", msix_table->msg_addr_hi);
                        sddf_dprintf("Vector 0 Message Data: 0x%x\n", msix_table->msg_data);
                        sddf_dprintf("Vector 0 Vector Control: 0x%x\n", msix_table->vec_ctrl);

                        uint32_t *msix_pba = (uint32_t *)0xFEBD5800;
                        sddf_dprintf("PBA: 0x%x\n", msix_pba[0]);
                    }

                    for (int j = 0; j < 256; j++) {
                        if (j && j % 16 == 0) sddf_dprintf("\n");
                        sddf_dprintf("%02x ", *(uint8_t *)(pci_bus + (i << 15) + (k << 12) + j));
                    }
                    sddf_dprintf("\n");

                    sddf_dprintf("pci header: 0x%lx\n", (uintptr_t)pci_header);
                    sddf_dprintf("MSI-X cap: 0x%lx\n", (uintptr_t)msix_cap);
                    uint16_t *test = (uint16_t *)((void *)pci_header + 0x98 + 2);
                    sddf_dprintf("test: 0x%x\n", *test);

                    struct msi_capability *msi_cap = (struct msi_capability *)find_pci_cap_by_id(pci_header, PCI_CAP_ID_MSI);
                    if (msi_cap) {
                        // Enable MSI
                    }
                }
            }
        }
    }
}

void pci_ecam_scan(uintptr_t ecam_base, uint8_t start_bus, uint8_t end_bus)
{
    for (int i = start_bus; i < end_bus; i++) {
        pci_bus_scan(ecam_base + (i << 20));
    }
}

void parse_mcfg(void *mcfg_addr)
{
    acpi_sdt_header_t *mcfg_header = (acpi_sdt_header_t *)mcfg_addr;
    uint32_t num_entries = (mcfg_header->length - sizeof(acpi_sdt_header_t)) / sizeof(mcfg_ecam_alloc_t);
    mcfg_ecam_alloc_t *ecam_alloc = (mcfg_ecam_alloc_t *)((uintptr_t)mcfg_addr + sizeof(acpi_sdt_header_t) + 8);

    // TODO: validate the checksum
    for (int i = 0; i < num_entries; i++) {
        sddf_dprintf("\nScan the buses [0x%02x-0x%02x] at 0x%lx\n", ecam_alloc[i].start_bus,
                     ecam_alloc[i].end_bus, ecam_alloc[i].base_addr);
        pci_ecam_scan(ecam_alloc[i].base_addr, ecam_alloc[i].start_bus, ecam_alloc[i].end_bus);
    }
}

void init(void)
{
    sddf_dprintf("PCIE|INFO: hello\n");
    sddf_dprintf("ecam_base: 0x%lx\n", (uintptr_t)(config.ecam_base));
    sddf_dprintf("ecam_size: 0x%lx\n", config.ecam_size);
    sddf_dprintf("bus_range: 0x%x\n", config.bus_range);

    void *rsdt_addr = rsdp_dump();
    void *mcfg_addr = find_sdt(rsdt_addr, "MCFG");
    parse_mcfg(mcfg_addr);
}

void notified(sddf_channel ch)
{

}
