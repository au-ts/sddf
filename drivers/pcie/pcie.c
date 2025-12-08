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

void rsdp_dump()
{
    for (char *addr = (char *)BIOS_AREA_START; addr < (char *)BIOS_AREA_END; addr += 16) {
        if (!strncmp(addr, "RSD PTR ", 8)) {
            sddf_dprintf("Found the identifier at 0x%lx:\n", (uintptr_t)addr);
            sddf_dprintf("%c%c%c%c%c%c%c%c\n", addr[0], addr[1], addr[2], addr[3], addr[4], addr[5], addr[6], addr[7]);

            // TODO: validate the checksum
            // TODO: return rsdt_addr
        }
    }

    // TODO:  return NULL
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
            }
        }
    }
}

void pci_ecam_scan(uintptr_t ecam_base, uint64_t ecam_size, uint8_t bus_range)
{
    for (int i = 0; i < bus_range; i++) {
        pci_bus_scan(ecam_base + (i << 20));
    }
}

void init(void)
{
    sddf_dprintf("PCIE|INFO: hello\n");
    sddf_dprintf("ecam_base: 0x%lx\n", (uintptr_t)(config.ecam_base));
    sddf_dprintf("ecam_size: 0x%lx\n", config.ecam_size);
    sddf_dprintf("bus_range: 0x%x\n", config.bus_range);

    pci_ecam_scan((uintptr_t)config.ecam_base, config.ecam_size, config.bus_range);

    rsdp_dump();
}

void notified(sddf_channel ch)
{

}
