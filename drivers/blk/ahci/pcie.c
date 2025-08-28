// @Tristan: YES this files style is shit :(
#include "pcie.h"

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_PCIE(...) do{ sddf_dprintf("PCIE |INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_PCIE(...) do{}while(0)
#endif
#define LOG_PCIE_ERR(...) do{ sddf_printf("PCIE |ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// MAKE SURE THESE MATCH meta.py
const uint64_t pcie_ecam_paddr = 0xe0000000;
const uint64_t pcie_ecam_vaddr = 0x600000000;
const uint64_t pcie_ecam_size = 0x10000000;
const uint64_t ahci_abar_paddr = 0xb0402000;
const uint64_t ahci_abar_vaddr = 0x700000000;
const uint64_t ahci_abar_size = 0x1000;

uint8_t sata_controller_bus;
uint8_t sata_controller_device;
uint8_t sata_controller_function;
bool found_sata_controller = false;

/* bus between [0, 256)
   device between [0, 31)
   function between [0, 8)
*/
uint64_t get_bdf_offset(uint8_t bus, uint8_t device, uint8_t function)
{
    /* [PCIe-2.0] Table 7-1 Enhanced Configuration Address Mapping */

    uint64_t offset = ((uint32_t)bus << 20) | ((uint32_t)device << 15) | ((uint32_t)function << 12);
    assert(offset % 4096 == 0); /* check page aligned */

    return offset;
}

static void device_print_and_set(uint8_t bus, uint8_t device, uint8_t function) {
    uint64_t offset = get_bdf_offset(bus, device, function);
    void *pcie_config_base = (void *)(pcie_ecam_vaddr + offset);
    volatile pcie_header_t *header = (pcie_header_t *)pcie_config_base;
    if (header->vendor_id == PCIE_VENDOR_INVALID) {
        return;
    }

    if (
        header->base_class_code == SATA_BASE_CLASS_CODE &&
        header->subclass_code == SATA_SUBCLASS_CODE &&
        header->class_code_programming_interface == AHCI_PROG_IF
    ) {
        LOG_PCIE("============= Found a SATA controller! ============\n");

        LOG_PCIE("\tB.D:F: %02x:%02x.%01x\n", bus, device, function);
        LOG_PCIE("\tvendor ID: 0x%04x\n", header->vendor_id);
        LOG_PCIE("\tdevice ID: 0x%04x\n", header->device_id);
        LOG_PCIE("\tcommand register: 0x%04x\n", header->command);
        LOG_PCIE("\tstatus register: 0x%04x\n", header->status);
        LOG_PCIE("\trevision ID: 0x%02x\n", header->revision_id);
        LOG_PCIE("\tbase-class code: 0x%02x | sub-class code: 0x%02x\n", header->base_class_code, header->subclass_code);

        if (!found_sata_controller) {
            assert(ahci_abar_vaddr != 0);
            assert(ahci_abar_size != 0);

            LOG_PCIE("Enabling PCIE bus mastering and memory accesses...\n");
            header->command |= BIT(2) | BIT(1);

            volatile pcie_header_type0_t *type0_header = (pcie_header_type0_t *)pcie_config_base;

            LOG_PCIE("Disabling MSI/MSIx...\n");

            // Type-0 capability pointer at 0x34 (DWORD-aligned; low 2 bits reserved)
            uint8_t cap_ptr = type0_header->capabilities_pointer & ~0x3;

            while (cap_ptr) {
                volatile uint8_t *cap = (volatile uint8_t *) type0_header + cap_ptr;
                uint8_t id  = cap[0];
                uint8_t nxt = cap[1] & ~0x3;

                if (id == 0x05) {                 // MSI
                    volatile uint16_t *ctl = (volatile uint16_t *)(cap + 2);
                    *ctl &= ~(uint16_t)BIT(0);    // clear MSI Enable
                } else if (id == 0x11) {          // MSI-X
                    volatile uint16_t *ctl = (volatile uint16_t *)(cap + 2);
                    *ctl &= ~(uint16_t)BIT(15);   // clear MSI-X Enable
                }
                cap_ptr = nxt;
            }

            LOG_PCIE("Enabling legacy INTx ...\n");
            header->command &= ~BIT(10);

            found_sata_controller = true;
            sata_controller_bus = bus;
            sata_controller_device = device;
            sata_controller_function = function;

            // AHCI HBAs expose ABAR in BAR5 (MMIO)
            uint32_t bar5 = type0_header->base_address_registers[5];
            uint64_t abar = (uint64_t)(bar5 & ~0xF);   // mask off flags

            if (abar == 0) {
                LOG_PCIE("ABAR is not already set\n");

                // The AHCI specification requires ABAR (BAR5) to be a 32-bit MMIO BAR.
                // That means the controller expects the OS/firmware to program an address in the 32-bit address space only.
                assert(ahci_abar_paddr <= UINT32_MAX);
                assert((ahci_abar_paddr & 0xF) == 0);

                // Disabling PCIE bus mastering and memory accesses while (re)programming BARs
                header->command &= ~BIT(1);

                type0_header->base_address_registers[5] = (uint32_t)(ahci_abar_paddr & 0xFFFFFFFF);

                // Re-enabling PCIE bus mastering and memory accesses
                header->command |= BIT(1) | BIT(2);
            } else {
                LOG_PCIE("ABAR is already set\n");
                assert(ahci_abar_paddr == abar);
            }

            LOG_PCIE("\theader type: 0x%02x\n", header->header_type);
            LOG_PCIE("\thas multi-functions: %s\n",
                         header->header_type & PCIE_HEADER_TYPE_HAS_MULTI_FUNCTIONS ? "yes" : "no");
            LOG_PCIE("\tlayout variant: 0x%02lx\n", header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK);

            if ((header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK) == PCIE_HEADER_TYPE_GENERAL) {
                for (int i = 0; i < 6; i++) {
                    uint32_t bar = type0_header->base_address_registers[i];
                    LOG_PCIE("BAR%01d raw val: %08x\n", i, bar);
                    if (bar == 0) {
                        LOG_PCIE("\tunimplemented\n");
                        continue;
                    }

                    if (bar & BIT(0)) {
                        LOG_PCIE("\tbase address for I/O\n");
                        LOG_PCIE("\taddress: 0x%08lx\n", bar & ~(BIT(0) | BIT(1)));
                    } else {
                        LOG_PCIE("\tbase address for memory\n");
                        switch ((bar & (BIT(1) | BIT(2))) >> 1) {
                        case 0b00:
                            LOG_PCIE("\ttype: 32-bit space\n");
                            LOG_PCIE("\tfull address: 0x%08lx\n", bar & ~(BIT(4) - 1));

                            uint16_t saved_cmd = header->command;
                            header->command = saved_cmd & ~(uint16_t)BIT(1); // disable MEM decode

                            uint32_t bar_save = bar;
                            type0_header->base_address_registers[i] = 0xFFFFFFFF;
                            uint32_t sz = type0_header->base_address_registers[i];

                            // clear mem flag bits [3:0]
                            sz &= ~(uint32_t)(BIT(0) | BIT(1) | BIT(2) | BIT(3));
                            sz = ~sz + 1;

                            // restore BAR and command
                            type0_header->base_address_registers[i] = bar_save;
                            header->command = saved_cmd;

                            LOG_PCIE("\tsize: 0x%lx\n", (unsigned long)sz);

                            if (i == 5) {
                                assert(sz <= ahci_abar_size);
                                assert((ahci_abar_paddr & (sz - 1)) == 0);
                            }
                            break;

                        case 0b10:
                            LOG_PCIE("\ttype: 64-bit space\n");
                            if (i >= 5) {
                                LOG_PCIE("\tspecified 64-bit in the last slot, ignoring...");
                                continue;
                            }

                            uint32_t bar_upper = type0_header->base_address_registers[i + 1];

                            LOG_PCIE("\tfull address: 0x%08x_%08lx\n", bar_upper, bar & ~(BIT(4) - 1));

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

                            LOG_PCIE("\tsize: 0x%lx\n", size_readback);

                            // The original value in the Base Address register is restored before re-enabling
                            // decode in the command register of the device.
                            type0_header->base_address_registers[i] = bar;
                            type0_header->base_address_registers[i + 1] = bar_upper;
                            header->command |= BIT(1);

                            i += 1; // skip one slot.
                            break;

                        default:
                            LOG_PCIE("\ttype: reserved\n");
                        }
                        LOG_PCIE("\tprefetchable: %s\n", bar & BIT(3) ? "yes" : "no");
                    }
                }
            }

            LOG_PCIE("(PIN-based) interrupt disable: %s\n", (header->command & BIT(10)) ? "is disabled" : "is not disabled");
            LOG_PCIE("(PIN-based) interrupt status: %s\n", (header->status & BIT(3)) ? "asserted" : "none");

            // 0xff (255) means "unknown" or "no connection" on interrupt line
            // interrupt pin: 0 = no, 1 => INTA#, 2 => INTB#, 3 => INTC#, 4 => INTD#
            LOG_PCIE("\t(PIN-based) interrupt line: %02x, interrupt pin: %02x\n", type0_header->interrupt_line, type0_header->interrupt_pin);
            LOG_PCIE("\tNOTE: ignore interrupt line under APIC/ACPI.\n");
            if (!(header->status & BIT(4))) {
                LOG_PCIE("no capabilities??\n");
            }; /* assert capabilities list status exists */
            LOG_PCIE("start capabilities PTR: %u\n", type0_header->capabilities_pointer);

            /* ach capability
            must be DWORD aligned. The bottom two bits of all pointers (including the initial pointer
            at 34h) are reserved and must be implemented as 00b although software must mask them to
            allow for future uses of these bits. A pointer value of 00h is used to indicate the last
            capability in the list.*/
            uint8_t current_ptr = type0_header->capabilities_pointer & ~0b11;
            /* process capabilities list to get MSI */
            while (current_ptr != 0) {
                volatile uint8_t *capability = (void *)(pcie_config_base + current_ptr);
                /* 6.8.1 of the pci spec */
                uint8_t cap_id = capability[0];
                LOG_PCIE("cap ptr: %x, id: %x\n", current_ptr, cap_id);
                uint8_t PCIE_CAPABILITY_ID_MSI = 0x05; /* #define this. */
                uint8_t PCIE_CAPABILITY_ID_MSIX = 0x11; /* #define this. */
                uint8_t PCIE_CAPABILITY_ID_PM = 0x1; /* #define this. */
                if (cap_id == PCIE_CAPABILITY_ID_MSI) {
                    uint16_t message_control = capability[2] | ((uint16_t)capability[3] << 8);
                    LOG_PCIE("\tmessage control(msi): %x\n", message_control);
                } else if (cap_id == PCIE_CAPABILITY_ID_MSIX) {
                    uint16_t message_control = capability[2] | ((uint16_t)capability[3] << 8);
                    LOG_PCIE("\tmessage control(msix): %x\n", message_control);
                } else if (cap_id == PCIE_CAPABILITY_ID_PM) {
                    // https://lekensteyn.nl/files/docs/PCI_Power_Management_12.pdf¸ §3.2
                    // not this...
                    uint16_t control = capability[4] | ((uint16_t)capability[5] << 8);
                    LOG_PCIE("\tpower management ctrl: %x\n", control);
                } else if (cap_id == 0x10 /* PCI Express */) {
                    LOG_PCIE("\troot control(pcie): %x\n", *(uint16_t *)&(capability[0x1C]));
                    LOG_PCIE("\troot status(pcie): %x\n", *(uint32_t *)&(capability[0x20]));
                } else {
                    LOG_PCIE("\tunknown\n");
                }

                current_ptr = (capability[1] & ~0b11);
            }

        } else {
            LOG_PCIE("FOUND another SATA controller. Do nothing...\n");
        }
    }

}

void print_pci_info(uint8_t bus, uint8_t device, uint8_t function, bool to_mask)
{
    uintptr_t offset = get_bdf_offset(bus, device, function);
    assert(offset < pcie_ecam_size);
    void *pcie_config_base = (void *)(pcie_ecam_vaddr + offset);
    volatile pcie_header_t *header = (pcie_header_t *)pcie_config_base;

    if (header->vendor_id == PCIE_VENDOR_INVALID) return;

    LOG_PCIE("PCIE SUMMARY:\n\n");
    LOG_PCIE("B.D:F: %02x:%02x.%01x\n", bus, device, function);
    LOG_PCIE("ACK: command register: 0x%04x\n", header->command);
    LOG_PCIE("ACK: status register: 0x%04x\n", header->status);
    LOG_PCIE("(PIN-based) interrupt disable: %s\n", (header->command & BIT(10)) ? "is disabled" : "is not disabled");
    LOG_PCIE("(PIN-based) interrupt status: %s\n", (header->status & BIT(3)) ? "asserted" : "none");
    LOG_PCIE("PCIE enum done!\n\n");

    return;
}

void pcie_init() {
    LOG_PCIE("Beginning PCIE enumeration through ECAM memory\n");
    assert(pcie_ecam_paddr != 0);
    assert(pcie_ecam_vaddr != 0);
    assert(pcie_ecam_size != 0);

    for (uint16_t bus = 0; bus <= 255; bus++) {
        for (uint8_t device = 0; device < 32; device++) {
            for (uint8_t function = 0; function < 8; function++) {
                uint64_t offset = get_bdf_offset((uint8_t)bus, device, function);
                if (offset >= pcie_ecam_size) {
                    return;
                }

                device_print_and_set((uint8_t)bus, device, function);
            }
        }
    }

    LOG_PCIE("Finished PCIE enumeration through ECAM memory\n");
}