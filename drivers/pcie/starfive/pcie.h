#pragma once

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