/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * driver for xHCI USB host controller.
 * TODO:
 *  - implement host controller
 *  - expose tinyUSB interface
 */

#include "xhci.h"
#include <os/sddf.h>

/* hardcoded PCI location - should be found from enumeration instead */
#define XHCI_PCI_BUS
#define XHCI_PCI_DEVICE
#define XHCI_PCI_FUNCTION

/* the below PCI stuff is copied from nvme.c */
#define PCI_CONFIG_ADDR_IOPORT_ID 1
#define PCI_CONFIG_DATA_IOPORT_ID 2
#define PCI_CONFIG_ADDR_PORT 0xCF8
#define PCI_CONFIG_DATA_PORT 0xCFC

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

void init() {

}

void notified(microkit_channel ch) {
    (void) ch;
}