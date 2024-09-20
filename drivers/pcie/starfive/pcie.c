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
    volatile pcie_header_t *header = (pcie_header_t *)config_base;

    if (header->vendor_id == PCIE_VENDOR_INVALID) {
        return;
    }

    /*
        See: plda_pcie_addr_valid() in U-Boot
        https://lore.kernel.org/u-boot/20230423105859.125764-2-minda.chen@starfivetech.com/

        In the secondary bus of host bridge, can only access bus device 0;
        all other devices are duplicates of device 0.

        @todo there appears to be some way to change the secondary bus number?
              see e.g. plda_pcie_config_write()
              so it might not always be bus number 1.
    */
    if (bus == 1 && device > 0) {
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

    sddf_dprintf("\thas multi-functions: %s\n", header->header_type & PCIE_HEADER_TYPE_HAS_MULTI_FUNCTIONS ? "yes" : "no");
    sddf_dprintf("\tlayout variant: 0x%02x\n", header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK);

    if ((header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK) == PCIE_HEADER_TYPE_GENERAL) {
        volatile pcie_header_type0_t *type0_header = (pcie_header_type0_t *)config_base;
        for (int i = 0; i < 6; i++) {
            uint32_t bar = type0_header->base_address_registers[i];
            sddf_dprintf("BAR%01d raw val: %08x\n", i, bar);
            if (bar == 0) {
                sddf_dprintf("\tunimplemented\n");
                continue;
            }

            if (bar & BIT(0)) {
                sddf_dprintf("\tbase address for I/O\n");
                sddf_dprintf("\taddress: 0x%08x\n", bar & ~(BIT(0) | BIT(1)));
            } else {
                sddf_dprintf("\tbase address for memory\n");
                sddf_dprintf("\ttype: ");
                switch ((bar & (BIT(1) | BIT(2))) >> 1) {
                    case 0b00:
                        sddf_dprintf("32-bit space\n");
                        sddf_dprintf("\tfull address: 0x%08x\n", bar & ~(BIT(4) - 1));
                        break;

                    case 0b10:
                        sddf_dprintf("64-bit space\n");
                        if (i >= 5) {
                            sddf_dprintf("\tspecified 64-bit in the last slot, ignoring...");
                            continue;
                        }

                        uint32_t bar_upper = type0_header->base_address_registers[i + 1];

                        sddf_dprintf("\tfull address: 0x%08x_%08x\n", bar_upper, bar & ~(BIT(4) - 1));

                        /* [PCI-3.0] 6.2.5.1 Address Maps (Implementation Note) p227*/

                        // Decode (I/O or memory) of a register is disabled via the command register before sizing a Base Address register.
                        header->command &= ~(BIT(1));

                        // calculate size.
                        type0_header->base_address_registers[i] = 0xffffffff;
                        type0_header->base_address_registers[i + 1] = 0xffffffff;

                        // read back
                        uint32_t size_lower = type0_header->base_address_registers[i];
                        uint32_t size_upper = type0_header->base_address_registers[i + 1];
                        uint64_t size_readback = ((uint64_t)size_upper << 32) | (size_lower);
                        // calculation can be done from the 32-bit value read by first clearing encoding information bits
                        // (bit 0 for I/O, bits 0-3 formemory), inverting all 32 bits (logical NOT), then incrementing by 1
                        size_readback &= ~(BIT(3) | BIT(2) | BIT(1) | BIT(0));
                        size_readback = ~size_readback;
                        size_readback += 1;

                        sddf_dprintf("\tsize: 0x%lx\n", size_readback);

                        // The original value in the Base Address register is restored before re-enabling
                        // decode in the command register of the device.
                        type0_header->base_address_registers[i] = bar;
                        type0_header->base_address_registers[i + 1] = bar_upper;
                        header->command |= BIT(1);


                        i += 1; // skip one slot.
                        break;

                    default:
                        sddf_dprintf("reserved\n");
                }
                sddf_dprintf("\tprefetchable: %s\n", bar & BIT(3) ? "yes" : "no");
            }
        }
    }
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
