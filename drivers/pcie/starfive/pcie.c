/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

/*
    References:

    [PCIe-2.0] PCI Express 2.0 Base Specification Revision 0.9 (Sep 11, 2006).
        https://community.intel.com/cipcp26785/attachments/cipcp26785/fpga-intellectual-property/8220/1/PCI_Express_Base_Specification_v20.pdf
*/

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
    void *base = (void *)(pcie_config + get_bdf_offset(bus, device, function));
    uint16_t vendor_id = *(uint16_t *)(&base[0x0]);
    if (vendor_id == 0xffff) {
        return;
    }

    sddf_dprintf("\nB.D.F: %02x.%02x.%01x\n", bus, device, function);
    sddf_dprintf("vendor ID: 0x%04x\n", vendor_id);
    sddf_dprintf("device ID: 0x%04x\n", *(uint16_t *)(&base[0x2]));
    sddf_dprintf("command register: 0x%04x\n", *(uint16_t *)(&base[0x4]));
    sddf_dprintf("status register: 0x%04x\n", *(uint16_t *)(&base[0x6]));
    sddf_dprintf("class code | revision ID: 0x%04x\n", *(uint32_t *)(&base[0x8]));
    // sddf_dprintf("cache line size: 0x%02x\n", base[0xC]);
    // sddf_dprintf("master latency timer: 0x%02x\n", base[0xD]);
    sddf_dprintf("header type: 0x%02x\n", *(uint8_t *)(&base[0xE]));
    sddf_dprintf("BIST: 0x%02x\n", *(uint8_t *)(&base[0xF]));
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
    sddf_dprintf("Done\n");
}

void notified(microkit_channel ch)
{
}
