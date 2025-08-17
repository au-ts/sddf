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

const uint64_t pcie_ecam_paddr = 0x80000000;
const uint64_t pcie_ecam_vaddr = 0x600000000;
const uint64_t pcie_ecam_size = 0x10000000;

const uint64_t ahci_abar_paddr = 0xaa180000;
const uint64_t ahci_abar_vaddr = 0x700000000;
const uint64_t ahci_abar_size = 0x80000;

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


// The only config this does is enable bus mastering and memory access
// And assigns bar5 if not set
static void device_print_and_set(uint8_t bus, uint8_t device, uint8_t function) {
	uint64_t offset = get_bdf_offset(bus, device, function);
   	void *pcie_config_base = (void *)(pcie_ecam_vaddr + offset);
    volatile pcie_header_t *header = (pcie_header_t *)pcie_config_base;
 	if (header->vendor_id == PCIE_VENDOR_INVALID) {
        return;
    }

    // LOG_PCIE("== B.D:F: %02x:%02x.%01x\n", bus, device, function);
    // LOG_PCIE("vendor ID: 0x%04x\n", header->vendor_id);
    // LOG_PCIE("device ID: 0x%04x\n", header->device_id);
    // LOG_PCIE("command register: 0x%04x\n", header->command);
    // LOG_PCIE("status register: 0x%04x\n", header->status);
    // LOG_PCIE("revision ID: 0x%02x\n", header->revision_id);
    // LOG_PCIE("base-class code: 0x%02x | sub-class code: 0x%02x\n", header->base_class_code, header->subclass_code);

    if (
    	header->base_class_code == SATA_BASE_CLASS_CODE &&
    	header->subclass_code == SATA_SUBCLASS_CODE &&
    	header->class_code_programming_interface == AHCI_PROG_IF &&
    	!found_sata
    ) {
        LOG_PCIE("FOUND SATA !!!\n");

    	LOG_PCIE("== B.D:F: %02x:%02x.%01x\n", bus, device, function);
	    LOG_PCIE("vendor ID: 0x%04x\n", header->vendor_id);
	    LOG_PCIE("device ID: 0x%04x\n", header->device_id);
	    LOG_PCIE("command register: 0x%04x\n", header->command);
	    LOG_PCIE("status register: 0x%04x\n", header->status);
	    LOG_PCIE("revision ID: 0x%02x\n", header->revision_id);
	    LOG_PCIE("base-class code: 0x%02x | sub-class code: 0x%02x\n", header->base_class_code, header->subclass_code);

    	if (!found_sata) {
    		assert(ahci_abar_vaddr != 0);
    		assert(ahci_abar_size != 0);

            // enable bus mastering... and memory accesses
            header->command |= BIT(2) | BIT(1);

            // Disbale legacy intx
            header->command |= BIT(10);

	        found_sata = true;
	        sata_bus = bus;
	        sata_device = device;
	        sata_function = function;

	        volatile pcie_header_type0_t *type0_header = (pcie_header_type0_t *)pcie_config_base;

	        // AHCI HBAs expose ABAR in BAR5 (MMIO)
	        // If you want to *read* where firmware mapped it:
	        uint32_t bar5 = type0_header->base_address_registers[5];
	        uint64_t abar = (uint64_t)(bar5 & ~0xF);   // mask off flags

	        // If firmware did NOT assign it
            if (abar == 0) {
                // Must be 32 bit
            	assert(ahci_abar_paddr <= UINT32_MAX);
            	assert((ahci_abar_paddr & 0xF) == 0);

                // Disable Memory Space while (re)programming BARs
                header->command &= ~BIT(1);

                type0_header->base_address_registers[5] = (uint32_t)(ahci_abar_paddr & 0xFFFFFFF0);

                // Re-enable MEM + Bus Master
                header->command |= BIT(1) | BIT(2);

                abar = ahci_abar_paddr & ~0xF;
            } else {
            	// Check it is what we mapped
            	LOG_PCIE("ABAR is already set\n");
            	assert(ahci_abar_paddr == abar);
            }

            // TODO: Check the size of bar5 to make sure we did it correctly


            LOG_PCIE("ABAR = 0x%llx\n", (unsigned long long)abar);
	    } else {
	    	LOG_PCIE("FOUND another SATA\n");
	    }
	}

    if (!found_sata) {
        return;
    }

   	// Just printing
    LOG_PCIE("header type: 0x%02x\n", header->header_type);

    LOG_PCIE("\thas multi-functions: %s\n",
                 header->header_type & PCIE_HEADER_TYPE_HAS_MULTI_FUNCTIONS ? "yes" : "no");
    LOG_PCIE("\tlayout variant: 0x%02lx\n", header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK);

    if ((header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK) == PCIE_HEADER_TYPE_GENERAL) {
        volatile pcie_header_type0_t *type0_header = (pcie_header_type0_t *)pcie_config_base;
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
                    break;

                case 0b10:
                    LOG_PCIE("\ttype: 64-bit space\n");
                    if (i >= 5) {
                        LOG_PCIE("\tspecified 64-bit in the last slot, ignoring...");
                        continue;
                    }

                    uint32_t bar_upper = type0_header->base_address_registers[i + 1];

                    LOG_PCIE("\tfull address: 0x%08x_%08lx\n", bar_upper, bar & ~(BIT(4) - 1));

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

//     /* mask out the interrupt... */
//     // https://elixir.bootlin.com/linux/v5.18-rc4/source/drivers/pci/pci.c#L4595
//     if (to_mask) {
//         header->command |= BIT(10);
//     } else {
//         header->command &= ~BIT(10);
//     }

//     // we only access IRQ PIn and Line an Capiblites which are actually comon (TODO)
//     // assert((header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK) == PCIE_HEADER_TYPE_GENERAL);
//     volatile pcie_header_type0_t *type0_header = (pcie_header_type0_t *)pcie_config_base;
//         // 0xff (255) means "unknown" or "no connection" on interrupt line
//     // interrupt pin: 0 = no, 1 => INTA#, 2 => INTB#, 3 => INTC#, 4 => INTD#
//     LOG_PCIE("\t(PIN-based) interrupt line: %02x, interrupt pin: %02x\n", type0_header->interrupt_line, type0_header->interrupt_pin);

//     if (!(header->status & BIT(4))) {
//         LOG_PCIE("no capabilities??\n");
//     }; /* assert capabilities list status exists */
//     LOG_PCIE("start capabilities PTR: %u\n", type0_header->capabilities_pointer);

//     /* ach capability
// must be DWORD aligned. The bottom two bits of all pointers (including the initial pointer
// at 34h) are reserved and must be implemented as 00b although software must mask them to
// allow for future uses of these bits. A pointer value of 00h is used to indicate the last
// capability in the list.*/
//     uint8_t current_ptr = type0_header->capabilities_pointer & ~0b11;
//     /* process capabilities list to get MSI */
//     while (current_ptr != 0) {
//         volatile uint8_t *capability = (void *)(pcie_config_base + current_ptr);
//         /* 6.8.1 of the pci spec */
//         uint8_t cap_id = capability[0];
//         LOG_PCIE("cap ptr: %x, id: %x\n", current_ptr, cap_id);
//         uint8_t PCIE_CAPABILITY_ID_MSI = 0x05; /* #define this. */
//         uint8_t PCIE_CAPABILITY_ID_MSIX = 0x11; /* #define this. */
//         uint8_t PCIE_CAPABILITY_ID_PM = 0x1; /* #define this. */
//         if (cap_id == PCIE_CAPABILITY_ID_MSI) {
//             uint16_t message_control = capability[2] | ((uint16_t)capability[3] << 8);
//             LOG_PCIE("\tmessage control(msi): %x\n", message_control);
//         } else if (cap_id == PCIE_CAPABILITY_ID_MSIX) {
//             uint16_t message_control = capability[2] | ((uint16_t)capability[3] << 8);
//             LOG_PCIE("\tmessage control(msix): %x\n", message_control);
//         } else if (cap_id == PCIE_CAPABILITY_ID_PM) {
//             // https://lekensteyn.nl/files/docs/PCI_Power_Management_12.pdf¸ §3.2
//             // not this...
//             uint16_t control = capability[4] | ((uint16_t)capability[5] << 8);
//             LOG_PCIE("\tpower management ctrl: %x\n", control);
//         } else if (cap_id == 0x10 /* PCI Express */) {
//             LOG_PCIE("\troot control(pcie): %x\n", *(uint16_t *)&(capability[0x1C]));
//             LOG_PCIE("\troot status(pcie): %x\n", *(uint32_t *)&(capability[0x20]));
//         } else {
//             LOG_PCIE("\tunknown\n");
//         }

//         current_ptr = (capability[1] & ~0b11);
//     }
}


void pcie_init() {
    LOG_PCIE("Beginning PCIE enumeration through ECAM memory\n");
    assert(pcie_ecam_paddr != 0);
    assert(pcie_ecam_vaddr != 0);
    assert(pcie_ecam_size != 0);

    for (uint8_t bus = 0; bus <= 255; bus++) {
        for (uint8_t device = 0; device < 32; device++) {
            for (uint8_t function = 0; function < 8; function++) {
            	if (found_sata) {
            		return;
            	}
                uint64_t offset = get_bdf_offset(bus, device, function);
                if (offset >= pcie_ecam_size) {
                    return;
                }

                device_print_and_set(bus, device, function);
            }
        }
    }
}