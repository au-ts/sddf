/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#include "pcie.h"

void *pcie_regs;

/* This is the PCI Enhanced Configuration Access Mechanism,
    See [PCIe-2.0] §7.22
*/
uintptr_t pcie_config;
#define PCIE_CONFIG_SIZE 0x1000000

/* bus between [0, 256)
   device between [0, 31)
   function between [0, 8)
*/
uintptr_t get_bdf_offset(uint8_t bus, uint8_t device, uint8_t function)
{
    /* [PCIe-2.0] Table 7-1 Enhanced Configuration Address Mapping */

    uintptr_t offset = ((uint32_t)bus << 20) | ((uint32_t)device << 15) | ((uint32_t)function << 12);

    assert(offset % 4096 == 0); /* check page aligned */

    return offset;
}

void device_print(uint8_t bus, uint8_t device, uint8_t function)
{
    void *config_base = (void *)(pcie_config + get_bdf_offset(bus, device, function));
    pcie_header_t *header = (pcie_header_t *)config_base;

    if (header->vendor_id == PCIE_VENDOR_INVALID) {
        return;
    }

    sddf_dprintf("\nB.D:F: %02x:%02x.%01x\n", bus, device, function);
    sddf_dprintf("vendor ID: 0x%04x\n", header->vendor_id);
    sddf_dprintf("device ID: 0x%04x\n", header->device_id);
    sddf_dprintf("command register: 0x%04x\n", header->command);
    sddf_dprintf("status register: 0x%04x\n", header->status);
    sddf_dprintf("revision ID: 0x%02x\n", header->revision_id);
    sddf_dprintf("base-class code: 0x%02x | sub-class code: 0x%02x\n", header->base_class_code, header->subclass_code);
    sddf_dprintf("header type: 0x%02x\n", header->header_type);
}

void init()
{
    sddf_dprintf("pcie driver starting!\n");

    for (uint8_t bus = 0; bus < 256; bus++) {
        for (uint8_t device = 0; device < 32; device++) {
            for (uint8_t function = 0; function < 8; function++) {
                uintptr_t offset = get_bdf_offset(bus, device, function);
                if (offset >= PCIE_CONFIG_SIZE) {
                    goto out;
                }

                device_print(bus, device, function);
            }
        }
    }

out:
    sddf_dprintf("\n\nPCIE_ENUM_COMPLETE\n");
}

void notified(microkit_channel ch)
{
}
