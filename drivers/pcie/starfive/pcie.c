/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#include "pcie.h"
#include "nvme.h"

// void *pcie_regs;

/* This is the PCI Enhanced Configuration Access Mechanism,
    See [PCIe-2.0] §7.22
*/
uintptr_t pcie_config;
#define PCIE_CONFIG_SIZE 0x1000000

volatile nvme_controller_t *nvme_controller;
volatile nvme_submission_queue_entry_t *nvme_asq_region;
volatile nvme_completion_queue_entry_t *nvme_acq_region;
uintptr_t nvme_asq_region_paddr;
uintptr_t nvme_acq_region_paddr;
#define NVME_ADMIN_QUEUE_SIZE 0x1000


uintptr_t data_region_paddr;
uint8_t *data_region;

/* TODO: don't hardcode */
#define NVME_ASQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / 64)
#define NVME_ACQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / 64)
_Static_assert(NVME_ASQ_CAPACITY <= 0x1000, "capacity of ASQ must be <=4096 (entries)");
_Static_assert(NVME_ACQ_CAPACITY <= 0x1000, "capacity of ACQ must be <=4096 (entries)");

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

    sddf_dprintf("\thas multi-functions: %s\n",
                 header->header_type & PCIE_HEADER_TYPE_HAS_MULTI_FUNCTIONS ? "yes" : "no");
    sddf_dprintf("\tlayout variant: 0x%02lx\n", header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK);

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
                sddf_dprintf("\taddress: 0x%08lx\n", bar & ~(BIT(0) | BIT(1)));
            } else {
                sddf_dprintf("\tbase address for memory\n");
                sddf_dprintf("\ttype: ");
                switch ((bar & (BIT(1) | BIT(2))) >> 1) {
                case 0b00:
                    sddf_dprintf("32-bit space\n");
                    sddf_dprintf("\tfull address: 0x%08lx\n", bar & ~(BIT(4) - 1));
                    break;

                case 0b10:
                    sddf_dprintf("64-bit space\n");
                    if (i >= 5) {
                        sddf_dprintf("\tspecified 64-bit in the last slot, ignoring...");
                        continue;
                    }

                    uint32_t bar_upper = type0_header->base_address_registers[i + 1];

                    sddf_dprintf("\tfull address: 0x%08x_%08lx\n", bar_upper, bar & ~(BIT(4) - 1));

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

/* [NVMe-2.1] 3.3.1 Memory-based Transport Queue Model (PCIe) */
void nvme_queue_init()
{
    // TODO.
}

void nvme_debug_dump_controller_regs()
{
    sddf_dprintf("CAP: %016lx\n", nvme_controller->cap);
    sddf_dprintf("VS: major: %u, minor: %u, tertiary: %u\n", nvme_controller->vs.mjr, nvme_controller->vs.mnr,
                 nvme_controller->vs.ter);
    sddf_dprintf("INTMS: %08x\n", nvme_controller->intms);
    sddf_dprintf("INTMC: %08x\n", nvme_controller->intmc);
    sddf_dprintf("CC: %08x\n", nvme_controller->cc);
    sddf_dprintf("CSTS: %08x\n", nvme_controller->csts);
    sddf_dprintf("AQA: %08x\n", nvme_controller->aqa);
    sddf_dprintf("ASQ: %016lx\n", nvme_controller->asq);
    sddf_dprintf("ACQ: %016lx\n", nvme_controller->acq);
}

/* [NVMe-2.1] 3.5.1 Memory-based Controller Initialization (PCIe) */
void nvme_controller_init()
{
    sddf_dprintf("CAP: %016lx\n", nvme_controller->cap);
    sddf_dprintf("VS: major: %u, minor: %u, tertiary: %u\n", nvme_controller->vs.mjr, nvme_controller->vs.mnr,
                 nvme_controller->vs.ter);
    sddf_dprintf("CC: %08x\n", nvme_controller->cc);


    nvme_controller->cc &= ~NVME_CC_EN;

    // 1. Wait for CSTS.RDY to become '0' (i.e. not ready)
    while (nvme_controller->csts & NVME_CSTS_RDY);

    // 2. Configure Admin Queue(s)
    assert(nvme_asq_region_paddr != 0x0);
    assert(nvme_acq_region_paddr != 0x0);
    nvme_controller->asq = nvme_asq_region_paddr;
    nvme_controller->acq = nvme_acq_region_paddr;
    nvme_controller->aqa &= ~(NVME_AQA_ACQS_MASK | NVME_AQA_ASQS_MASK);
    nvme_controller->aqa |= ((NVME_ASQ_CAPACITY - 1) << NVME_AQA_ASQS_SHIFT)
                          | ((NVME_ACQ_CAPACITY - 1) << NVME_AQA_ACQS_SHIFT);

    // 3. Initialise Command Support Sets.
    nvme_controller->cc &= ~(NVME_CC_CSS_MASK);
    if (nvme_controller->cap & NVME_CAP_NOIOCSS) {
        nvme_controller->cc |= 0b111 << NVME_CC_CSS_SHIFT;
    } else if (nvme_controller->cap & NVME_CAP_IOCSS) {
        nvme_controller->cc |= 0b110 << NVME_CC_CSS_SHIFT;
    } else if (nvme_controller->cap & NVME_CAP_NCSS) {
        nvme_controller->cc |= 0b000 << NVME_CC_CSS_SHIFT;
    }

    // 4a. Arbitration Mechanism (TODO)
    // 4b. Memory Page Size
    nvme_controller->cc &= ~NVME_CC_MPS_MASK;
    /* n.b. page size = 2 ^ (12 + MPS) */
    nvme_controller->cc |= ((PAGE_SIZE >> 12) << NVME_CC_MPS_SHIFT) & NVME_CC_MPS_MASK;

    // TODO: See initialisation note under §4.2.4; fine since already that way.

    // 5. Enable the controller
    nvme_controller->cc |= NVME_CC_EN;

    // 6. Wait for ready
    sddf_dprintf("waiting ready...\n");
    while (!(nvme_controller->csts & NVME_CSTS_RDY));
    sddf_dprintf("\tdone\n");

    // 7. Send the Identify Controller command (Identify with CNS = 01h)
    uint8_t DSTRD = (nvme_controller->cap & NVME_CAP_DSTRD_MASK) >> NVME_CAP_DSTRD_SHIFT;
    uint16_t sq_tail = nvme_sqytdbl_read(nvme_controller, DSTRD, 0);
    uint16_t cq_head = nvme_cqyhdbl_read(nvme_controller, DSTRD, 0);
    sddf_dprintf("admin tail: %u\n", sq_tail);
    sddf_dprintf("admin head: %u\n", cq_head);

    // Identify Command (5.1.13)
    nvme_asq_region[sq_tail] = (nvme_submission_queue_entry_t){
        .cdw0 = /* CID */ (0b1111 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x6,
        .cdw10 = /* CNTID[31:16] */ 0x0 | /* CNS */ 0x01,
        .dptr_hi = 0,
        .dptr_lo = data_region_paddr, /* TEMP */
    };

    uint32_t orig_dw3 = ((volatile uint32_t *)nvme_acq_region)[3];
    sddf_dprintf("orig dw3: %x\n", orig_dw3);

    // todo: overflow?
    nvme_sqytdbl_write(nvme_controller, DSTRD, 0, ++sq_tail);

    nvme_debug_dump_controller_regs();

    // 4.2.4.1 shows how to send commands
    sddf_dprintf("waiting for completed command...\n")
    while (!(nvme_acq_region[cq_head].phase_tag_and_status & BIT(0)));
    sddf_dprintf("complete\n");


    // sddf_dprintf("new submission tail: %u\n", nvme_sqytdbl_read(nvme_controller, DSTRD, 0));
    // sddf_dprintf("waiting completion queue change...\n");
    // uint16_t orig_cq_head = cq_head;
    // while (cq_head == orig_cq_head) {
    //     cq_head = nvme_cqyhdbl_read(nvme_controller, DSTRD, 0);
    // }
    // sddf_dprintf("\tdone\n");

    sddf_dprintf("new head: %u\n", cq_head);
    // sudo nvme admin-passthru /dev/nvme0 --opcode=0x06 --cdw10=0x0001 --data-len=4096 -r  -s
    for (int i = 0; i < 64; i++) {
        sddf_dprintf("[%04x]: %x: %c\n", i, data_region[i], data_region[i]);
    }
}

void nvme_init()
{
    sddf_dprintf("Starting NVME config...\n");

    // We should do a Function Level Reset as defined by [PCIe-2.0] spec §6.6.2

    // https://github.com/bootreer/vroom/blob/d8bbe9db2b1cfdfc38eec31f3b48f5eb167879a9/src/nvme.rs#L220

    nvme_controller_init();
    nvme_queue_init();
}

void init()
{
    sddf_dprintf("pcie driver starting!\n");

    for (uint8_t bus = 0; bus <= 255; bus++) {
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

    nvme_init();
}

/* See: 3.3 NVM Queue MOdels */
// CAP.MQES

void notified(microkit_channel ch)
{
}
