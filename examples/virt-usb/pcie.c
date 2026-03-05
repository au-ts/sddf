#include <sddf/util/printf.h>
#include <os/sddf.h>

/*
    References:

    [PCIe-2.0] PCI Express 2.0 Base Specification Revision 0.9 (Sep 11, 2006).
        https://community.intel.com/cipcp26785/attachments/cipcp26785/fpga-intellectual-property/8220/1/PCI_Express_Base_Specification_v20.pdf

    [PCI-3.0] PCI Local Bus Specification Revision 3.0 (Feb 3, 2004)
        https://lekensteyn.nl/files/docs/PCI_SPEV_V3_0.pdf
*/

/* [PCIe-2.0] §7.5 PCI-Compatible Configuration Registers
   [PCI-3.0] §6.1 Configuration Space Organization

   All of these registers are read-only.
*/
typedef struct pcie_header {
    /* This field identifies the manufacturer of the device.
       FFFFh is an invalid value for Vendor ID. */
    uint16_t vendor_id;
    /* This field identifies the particular device.
       This identifier is allocated by the vendor.*/
    uint16_t device_id;
    /* Provides coarse control over a device's ability to generate and respond to PCI cycles.
       See [PCI-3.0] §6.2.2 Device Control   and    [PCIe-2.0] §7.5.1.1 */
    uint16_t command;
    /* The Status register is used to record status information for PCI bus related events.
       See [PCI-3.0] §6.2.3 Device Status    and    [PCIe-2.0] §7.5.1.2 */
    uint16_t status;
    /*
        This register specifies a device specific revision identifier. The value
        is chosen by the vendor. Zero is an acceptable value. This field
        should be viewed as a vendor defined extension to the Device ID.
    */
    uint8_t revision_id;
    /* A specific register-level programming interface (if any). */
    uint8_t class_code_programming_interface;
    /* sub-class code which identifies more specifically the function of the device*/
    uint8_t subclass_code;
    /* Broadly classifies the type of function the device performs. */
    uint8_t base_class_code;
    /* This field is implemented by PCI Express devices as a read-write field
       for legacy compatibility purposes but has no effect on any PCI Express
       device behavior. */
    uint8_t cacheline_size;
    /* The Latency Timer does not apply to PCI Express. */
    uint8_t latency_timer;
    /* This byte identifies the layout of the second part of the predefined header. */
    uint8_t header_type;
    /* Built-in Self Test. Optional. */
    uint8_t bist;
} __attribute__((packed)) pcie_header_t;

_Static_assert(sizeof(pcie_header_t) == 16, "PCI Common Configuration Space Header must be 16 bytes");

#define PCIE_VENDOR_INVALID 0xffff

#define PCIE_HEADER_TYPE_HAS_MULTI_FUNCTIONS BIT(7)

#define PCIE_HEADER_TYPE_LAYOUT_MASK    (BIT(7) - 1)
#define PCIE_HEADER_TYPE_GENERAL        0x00
#define PCIE_HEADER_TYPE_PCI_PCI_BRIDGE 0x01

/* [PCIe-2.0] §7.5.2 Type 0 Configuration Space Header */
typedef struct pcie_header_type0 {
    pcie_header_t common_header;
   /* [PCI-3.0] 6.2.5. Base Addresses
      Base Address Registers (BAR) can be 32-bit (1 slot) or 64-bit (2 slots).
   */
    uint32_t base_address_registers[6];
   /* Points to the Card Information Structure (CIS) for a CardBus card. */
    uint32_t cardbus_cis_pointer;
    uint16_t subsystem_vendor_id;
    uint16_t subsystem_id;
    uint32_t expansion_rom_base_address;
    uint8_t capabilities_pointer;
    uint8_t _reserved[7];
    uint8_t interrupt_line;
    uint8_t interrupt_pin;
    uint8_t min_gnt;
    uint8_t max_lat;
} __attribute__((packed)) pcie_header_type0_t;

_Static_assert(sizeof(pcie_header_type0_t) == 64, "Type 0 Configuration Space Header must be 64 bytes");


uintptr_t pcie_config = 0x20000000; // don't like this being hardcoded but cannot figure out that part of sddfgen
uintptr_t ehci_regs = 0x30000000;


sddf_channel pcie_channel = 3;

static bool found_ehci = false;
static uint8_t ehci_bus;
static uint8_t ehci_device;
static uint8_t ehci_function;

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
    uintptr_t offset = get_bdf_offset(bus, device, function);
    assert(offset < PCIE_CONFIG_SIZE);
    void *config_base = (void *)(pcie_config + offset);
    volatile pcie_header_t *header = (pcie_header_t *)config_base;

    if (header->vendor_id == PCIE_VENDOR_INVALID) {
        // sddf_printf("invalid vendor ID=0x%x, continue...\n", header->vendor_id);
        return;
    }

    sddf_dprintf("\nB.D:F: %02x:%02x.%01x\n", bus, device, function);
    sddf_dprintf("vendor ID: 0x%04x\n", header->vendor_id);
    sddf_dprintf("device ID: 0x%04x\n", header->device_id);
    sddf_dprintf("command register: 0x%04x\n", header->command);
    sddf_dprintf("status register: 0x%04x\n", header->status);
    sddf_dprintf("revision ID: 0x%02x\n", header->revision_id);
    sddf_dprintf("base-class code: 0x%02x | sub-class code: 0x%02x\n", header->base_class_code, header->subclass_code);

    sddf_dprintf("enabled bus master and memory access\n");

    sddf_dprintf("header type: 0x%02x\n", header->header_type);

    sddf_dprintf("\thas multi-functions: %s\n",
                 header->header_type & PCIE_HEADER_TYPE_HAS_MULTI_FUNCTIONS ? "yes" : "no");
    sddf_dprintf("\tlayout variant: 0x%02lx\n", header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK);

    /* enable EHCI device */
    if (header->base_class_code == 0x0c && header->subclass_code == 0x03 && !found_ehci) {
        sddf_printf("enabling ehci pci device..\n");
        found_ehci = true;
        ehci_bus = bus;
        ehci_device = device;
        ehci_function = function;
        volatile pcie_header_type0_t *type0_header = (pcie_header_type0_t *) config_base;
        header->command &= ~BIT(1);
        type0_header->base_address_registers[0] = 0x38000000;
        type0_header->base_address_registers[1] = 0;
        header->command |= BIT(1);
    }

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
                    
                    sddf_printf("negotiate BAR...\n");


                    header->command &= ~(BIT(1));

                    type0_header->base_address_registers[i] = 0xffffffff;

                    uint32_t bar_size = type0_header->base_address_registers[i];
                    
                    bar_size &= ~(BIT(3) | BIT(2) | BIT(1) | BIT(0));
                    bar_size = ~bar_size;
                    bar_size += 1;

                    sddf_dprintf("\tsize: 0x%x\n", bar_size);

                    type0_header->base_address_registers[i] = bar;                    

                    header->command |= BIT(1);


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

void print_pci_info(uint8_t bus, uint8_t device, uint8_t function, bool to_mask)
{
    uintptr_t offset = get_bdf_offset(bus, device, function);
    assert(offset < PCIE_CONFIG_SIZE);
    void *config_base = (void *)(pcie_config + offset);
    volatile pcie_header_t *header = (pcie_header_t *)config_base;

    if (header->vendor_id == PCIE_VENDOR_INVALID) return;

    sddf_dprintf("\nB.D:F: %02x:%02x.%01x\n", bus, device, function);
    sddf_dprintf("ACK: command register: 0x%04x\n", header->command);
    sddf_dprintf("ACK: status register: 0x%04x\n", header->status);
    sddf_dprintf("\t(PIN-based) interrupt disable: %s\n", (header->command & BIT(10)) ? "is disabled" : "is not disabled");
    sddf_dprintf("\t(PIN-based) interrupt status: %s\n", (header->status & BIT(3)) ? "asserted" : "none");

    // return;

    /* mask out the interrupt... */
    // https://elixir.bootlin.com/linux/v5.18-rc4/source/drivers/pci/pci.c#L4595
    if (to_mask) {
        header->command |= BIT(10);
    } else {
        header->command &= ~BIT(10);
    }

    // we only access IRQ PIn and Line an Capiblites which are actually comon (TODO)
    // assert((header->header_type & PCIE_HEADER_TYPE_LAYOUT_MASK) == PCIE_HEADER_TYPE_GENERAL);
    volatile pcie_header_type0_t *type0_header = (pcie_header_type0_t *)config_base;
        // 0xff (255) means "unknown" or "no connection" on interrupt line
    // interrupt pin: 0 = no, 1 => INTA#, 2 => INTB#, 3 => INTC#, 4 => INTD#
    sddf_printf("\t(PIN-based) interrupt line: %02x, interrupt pin: %02x\n", type0_header->interrupt_line, type0_header->interrupt_pin);

    if (!(header->status & BIT(4))) {
        sddf_dprintf("no capabilities??\n");
    }; /* assert capabilities list status exists */
    sddf_dprintf("start capabilities PTR: %u\n", type0_header->capabilities_pointer);

    /* ach capability
must be DWORD aligned. The bottom two bits of all pointers (including the initial pointer
at 34h) are reserved and must be implemented as 00b although software must mask them to
allow for future uses of these bits. A pointer value of 00h is used to indicate the last
capability in the list.*/
    uint8_t current_ptr = type0_header->capabilities_pointer & ~0b11;
    /* process capabilities list to get MSI */
    while (current_ptr != 0) {
        volatile uint8_t *capability = (void *)(config_base + current_ptr);
        /* 6.8.1 of the pci spec */
        uint8_t cap_id = capability[0];
        sddf_dprintf("cap ptr: %x, id: %x\n", current_ptr, cap_id);
        uint8_t PCIE_CAPABILITY_ID_MSI = 0x05; /* #define this. */
        uint8_t PCIE_CAPABILITY_ID_MSIX = 0x11; /* #define this. */
        uint8_t PCIE_CAPABILITY_ID_PM = 0x1; /* #define this. */
        if (cap_id == PCIE_CAPABILITY_ID_MSI) {
            uint16_t message_control = capability[2] | ((uint16_t)capability[3] << 8);
            sddf_dprintf("\tmessage control(msi): %x\n", message_control);
        } else if (cap_id == PCIE_CAPABILITY_ID_MSIX) {
            uint16_t message_control = capability[2] | ((uint16_t)capability[3] << 8);
            sddf_dprintf("\tmessage control(msix): %x\n", message_control);
        } else if (cap_id == PCIE_CAPABILITY_ID_PM) {
            // https://lekensteyn.nl/files/docs/PCI_Power_Management_12.pdf¸ §3.2
            // not this...
            uint16_t control = capability[4] | ((uint16_t)capability[5] << 8);
            sddf_dprintf("\tpower management ctrl: %x\n", control);
        } else if (cap_id == 0x10 /* PCI Express */) {
            sddf_dprintf("\troot control(pcie): %x\n", *(uint16_t *)&(capability[0x1C]));
            sddf_dprintf("\troot status(pcie): %x\n", *(uint32_t *)&(capability[0x20]));
        } else {
            sddf_dprintf("\tunknown\n");
        }

        current_ptr = (capability[1] & ~0b11);
    }
}


void init(void)
{
    sddf_printf("pcie_config at 0x%lx\n", pcie_config);
    sddf_printf("enumerating pcie...\n");

    for (uint8_t bus = 0; bus <= 255; bus++) {
        for (uint8_t device = 0; device < 32; device++) {

            // for (uint8_t function = 0; function < 8; function++) {
            for (uint8_t function = 0; function < 8; function++) {
                // sddf_printf("enumerating at bus=%d, device=%d, function=%d, vaddr=0x%lx\n", bus, device, function, pcie_config + get_bdf_offset(bus, device, function));
                uintptr_t offset = get_bdf_offset(bus, device, function);
                if (offset >= PCIE_CONFIG_SIZE) {
                    goto enum_done;
                }

                /* TODO: This also configures BARs for the NVMe devices... */
                /* That is not printing. */
                device_print(bus, device, function);
            }
        }
    }

enum_done:

    assert(found_ehci);

    print_pci_info(ehci_bus, ehci_device, ehci_function, false);

    sddf_notify(pcie_channel);

    // print_ehci();

    sddf_printf("complete\n");
}

void notified(sddf_channel ch)
{
    sddf_printf("pcie notified?\n");
}

