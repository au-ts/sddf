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

static volatile struct xhci_op_regs* xhci_op_regs;
static volatile struct xhci_cap_regs* xhci_cap_regs;
static volatile struct xhci_runtime_regs* xhci_runtime_regs;
static volatile struct xhci_doorbell_regs* xhci_doorbell_regs;
static volatile struct xhci_device_context_base_address_array* xhci_dcbaa;

#define XHCI_PADDR 
#define XHCI_VADDR 0x20000000

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

#define DMA_START (0x70000000)
#define DMA_END (DMA_START + 0x40000)

uint64_t dma_bump = DMA_START;

void *dmalloc(int nbytes, int aligned_to) {
    uint64_t align_by = (dma_bump % aligned_to);
    if (align_by) {
        align_by = aligned_to - align_by;
    } else {
        align_by = 0;
    }

    if (dma_bump + align_by > DMA_END) {
        LOG_XHCI("out of DMA!\n");
        return NULL;
    }
    dma_bump += align_by;

    if (dma_bump + nbytes > DMA_END) {
        LOG_XHCI("out of DMA!\n");
        return NULL;
    }

    void *allocated = (void *) dma_bump;
    dma_bump += nbytes;
    return allocated;
}

void xhci_init() {
    /* set up regs */
    xhci_cap_regs = (void *) XHCI_VADDR;
    xhci_op_regs = (void *) XHCI_VADDR + xhci_cap_regs->caplength;
    xhci_runtime_regs = (void *) XHCI_VADDR + xhci_cap_regs->rtsoff;
    xhci_doorbell_regs = (void *) XHCI_VADDR + xhci_cap_regs->dboff;

    /* stop controller */
    xhci_op_regs->usb_cmd.structured.rs = 0;

    /* spin until controller halted */
    while (!xhci_op_regs->usb_sts.structured.hch);

    /* reset controller */
    xhci_op_regs->usb_cmd.structured.hcrst = 1;

    /* spin until controller reset and ready */
    while (xhci_op_regs->usb_cmd.structured.hcrst || xhci_op_regs->usb_sts.structured.cnr);

    /* spin until ready */
    LOG_XHCI("controller ready for init!\n");

    /* program max device slots enabled */
    xhci_op_regs->config.structured.max_slots_en = XHCI_MAX_DEVICE_SLOTS;

    /* program device context base address array pointer  (DCBAAP)*/    
    xhci_dcbaa = dmalloc(sizeof(struct xhci_device_context_base_address_array), 1);

    /* element 0: scratchpad buffers - QEMU doesn't use any */
    int n_scratchpads = xhci_cap_regs->hcsparams2.structured.max_sp_buf_hi << 5;
    n_scratchpads |= xhci_cap_regs->hcsparams2.structured.max_sp_buf_lo;
    if (n_scratchpads > XHCI_MAX_SCRATCHPADS) {
        LOG_XHCI("too many scratchpads!\n");
        return;
    }

    if (n_scratchpads) {
        LOG_XHCI("not implemented\n");
        return;
    }

    /* elements 1->max_slots_en: device_context ptrs, initially 0 */
    for (int i = 0; i < XHCI_MAX_DEVICE_SLOTS - 1; i++) {
        xhci_dcbaa->device_contexts[i] = NULL;
    }

    xhci_op_regs->dcbaap = (uint64_t) xhci_dcbaa;
    
    /* set up command ring: program command ring control register (CRCR)*/
     
    /* initialise event ring */

    /* set up interrupter 0 (use pin based) */

    /* enable interrupts */

    /* start the controller again */

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

    xhci_init();
}

void notified(microkit_channel ch) {
    (void) ch;
}