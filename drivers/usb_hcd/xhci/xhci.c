/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * driver for xHCI USB host controller.
 * TODO:
 *  - implement host controller
 *    - implement PCI intialisation
 *    - implement reset xHCI driver
 *    - implement set up xHCI driver
 *    - implement TRB handling and figure out interface to this driver
 *  - expose tinyUSB interface
 */

#include "xhci.h"
#include <os/sddf.h>
#include <sddf/util/printf.h>

/* hardcoded PCI location - should be found from enumeration instead. 
 * (this is set using qemu arguments, not appropriate for real x86 board)
 */
#define XHCI_PCI_BUS 0
#define XHCI_PCI_DEVICE 5
#define XHCI_PCI_FUNCTION 0

/* the below PCI stuff is copied from nvme.c and also replicated in usb build scripts */
#define PCI_CONFIG_ADDR_IOPORT_ID 1
#define PCI_CONFIG_DATA_IOPORT_ID 2
#define PCI_CONFIG_ADDR_PORT 0xCF8
#define PCI_CONFIG_DATA_PORT 0xCFC

#define LOG_XHCI(...) do { sddf_dprintf("XHCI: "); sddf_dprintf(__VA_ARGS__); } while(0)

static volatile void* xhci_regs;

static uint32_t pci_config_read_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset)
{
    uint32_t address = (uint32_t)((uint32_t)bus << 16) | ((uint32_t)dev << 11) | ((uint32_t)func << 8) | (offset & 0xfc)
                     | ((uint32_t)0x80000000);
    microkit_x86_ioport_write_32(PCI_CONFIG_ADDR_IOPORT_ID, PCI_CONFIG_ADDR_PORT, address);
    return microkit_x86_ioport_read_32(PCI_CONFIG_DATA_IOPORT_ID, PCI_CONFIG_DATA_PORT);
}

static void pci_config_write_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset, uint32_t value)
{
    uint32_t address = (uint32_t)((uint32_t)bus << 16) | ((uint32_t)dev << 11) | ((uint32_t)func << 8) | (offset & 0xfc)
                     | ((uint32_t)0x80000000);
    microkit_x86_ioport_write_32(PCI_CONFIG_ADDR_IOPORT_ID, PCI_CONFIG_ADDR_PORT, address);
    microkit_x86_ioport_write_32(PCI_CONFIG_DATA_IOPORT_ID, PCI_CONFIG_DATA_PORT, value);
}

void xhci_init() {
    /* stop */
    
    /* set up rings */

    /* set up interrupters */
    
    /* start */


}

void init() {
    uint32_t vid_did = pci_config_read_32(XHCI_PCI_BUS, XHCI_PCI_DEVICE, XHCI_PCI_FUNCTION, 0x00);
    LOG_XHCI("VendorID:DeviceID = %08x\n", vid_did);

    uint32_t bar0 = pci_config_read_32(XHCI_PCI_BUS, XHCI_PCI_DEVICE, XHCI_PCI_FUNCTION, 0x10);
    LOG_XHCI("BAR0 readback: %08x\n", bar0);

    /* could use MSI-X interrupts, but not sure if SDDFgen supports them? */
    uint32_t intr_info = pci_config_read_32(XHCI_PCI_BUS, XHCI_PCI_DEVICE, XHCI_PCI_FUNCTION, 0x3C);
    uint8_t intr_line = intr_info & 0xFF;
    uint8_t intr_pin = (intr_info >> 8) & 0xFF;
    LOG_XHCI("PCI Interrupt Line: %d, Pin: %d\n", intr_line, intr_pin);

    /* hardcoded from meta.py */
    xhci_regs = (void*) 0x20000000;

    xhci_init();
}

void notified(microkit_channel ch) {
    (void) ch;
}