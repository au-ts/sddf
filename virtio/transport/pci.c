/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/virtio/common.h>
#include <sddf/virtio/transport/common.h>
#include <sddf/virtio/transport/pci.h>
#include <sddf/resources/device.h>

// @billn fix everything about this file...

#define VADDR_COMMON 0x60000000
#define VADDR_ISR 0x60001000
#define VADDR_DEVICE 0x60002000
#define VADDR_NOTIFY 0x60003000

#define PCI_ADDR_PORT_ID 1
#define PCI_ADDR_PORT_ADDR 0xCF8
#define PCI_DATA_PORT_ID 2
#define PCI_DATA_PORT_ADDR 0xCFC

uint32_t nftn_multiplier;

uint32_t pci_compute_port_address(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off) {
    uint32_t lbus  = (uint32_t)bus;
    uint32_t ldev = (uint32_t)dev;
    uint32_t lfunc = (uint32_t)func;

    // Bit 31     | Bits 30-24 | Bits 23-16 | Bits 15-11    | Bits 10-8       | Bits 7-0
    // Enable Bit | Reserved   | Bus Number | Device Number | Function Number | Register Offset

    /* Write enable bit */
    uint32_t addr = BIT(31);

    /* Shift in the PCI device address and register offset. */
    addr = addr | (lbus << 16) | (ldev << 11) | (lfunc << 8) | (off & 0xFC);

    return addr;
}

uint32_t pci_read_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off) {
    uint32_t addr = pci_compute_port_address(bus, dev, func, off);

    /* Write the address into the "select" port, then the data will be available at the "data" port. */
    seL4_X86_IOPort_Out32(microkit_ioport_cap(PCI_ADDR_PORT_ID), PCI_ADDR_PORT_ADDR, addr);
    return seL4_X86_IOPort_In32(microkit_ioport_cap(PCI_DATA_PORT_ID), PCI_DATA_PORT_ADDR).result;
}

void pci_write_16(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off, uint16_t data) {
    uint32_t addr = pci_compute_port_address(bus, dev, func, off);
    seL4_X86_IOPort_Out32(microkit_ioport_cap(PCI_ADDR_PORT_ID), PCI_ADDR_PORT_ADDR, addr);
    seL4_X86_IOPort_Out16(microkit_ioport_cap(PCI_DATA_PORT_ID), PCI_DATA_PORT_ADDR, data);
}

void pci_write_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off, uint32_t data) {
    uint32_t addr = pci_compute_port_address(bus, dev, func, off);
    seL4_X86_IOPort_Out32(microkit_ioport_cap(PCI_ADDR_PORT_ID), PCI_ADDR_PORT_ADDR, addr);
    seL4_X86_IOPort_Out32(microkit_ioport_cap(PCI_DATA_PORT_ID), PCI_DATA_PORT_ADDR, data);
}

virtio_pci_common_cfg_t *get_cfg(device_resources_t *device_resources)
{
    return (virtio_pci_common_cfg_t *) VADDR_COMMON;
}

void pci_debug_print_header(uint8_t bus, uint8_t dev, uint8_t func) {
    /* A PCI header is always 256-bytes long */
    uint32_t pci_header_regs[16];

    /* Read the first 4 32-bits header registers to work out the header type. */
    for (int i = 0; i < 4; i++) {
        pci_header_regs[i] = pci_read_32(bus, dev, func, i * 4);
    }

    uint16_t dev_id       = pci_header_regs[0] >> 16;
    uint16_t ven_id       = pci_header_regs[0] & 0xffff;
    uint16_t status       = pci_header_regs[1] >> 16;
    uint16_t cmd          = pci_header_regs[1] & 0xffff;
    uint8_t class_code    = pci_header_regs[2] >> 24;
    uint8_t subclass      = (pci_header_regs[2] >> 16) & 0xff;
    uint8_t progif        = (pci_header_regs[2] >> 8) & 0xff;
    uint8_t rev_id        = pci_header_regs[2] & 0xff;
    uint8_t bist          = pci_header_regs[3] >> 24;
    uint8_t hdr_type      = (pci_header_regs[3] >> 16) & 0xff;
    uint8_t latency_timer = (pci_header_regs[3] >> 8) & 0xff;
    uint8_t cache_line_sz = pci_header_regs[3] & 0xff;

    if (hdr_type != 0) {
        LOG_VIRTIO_TRANSPORT("printing non device pci header is unsupported.\n");
    }

    // https://wiki.osdev.org/PCI
    LOG_VIRTIO_TRANSPORT("pci_debug_print_header: bus %u, dev %u, func%u:\n", bus, dev, func);
    LOG_VIRTIO_TRANSPORT("\tDevice ID: 0x%x\n", dev_id);
    LOG_VIRTIO_TRANSPORT("\tVendor ID: 0x%x\n", ven_id);
    LOG_VIRTIO_TRANSPORT("\tStatus: 0x%x\n", status);
    LOG_VIRTIO_TRANSPORT("\tCommand: 0x%x\n", cmd);
    LOG_VIRTIO_TRANSPORT("\tClass code: 0x%x\n", class_code);
    LOG_VIRTIO_TRANSPORT("\tSubclass: 0x%x\n", subclass);
    LOG_VIRTIO_TRANSPORT("\tProgramming Interface: 0x%x\n", progif);
    LOG_VIRTIO_TRANSPORT("\tRevision ID: 0x%x\n", rev_id);
    LOG_VIRTIO_TRANSPORT("\tBuilt-in Self Test: 0x%x\n", bist);
    LOG_VIRTIO_TRANSPORT("\tHeader type: a general device\n");
    LOG_VIRTIO_TRANSPORT("\tLatency timer: 0x%x\n", latency_timer);
    LOG_VIRTIO_TRANSPORT("\tCache line size: 0x%x\n", cache_line_sz);

    /* Now read the rest of the header registers */
    for (int i = 4; i < 16; i++) {
        pci_header_regs[i] = pci_read_32(bus, dev, func, i * 4);
    }

    for (int i = 0; i < 6; i++) {
        LOG_VIRTIO_TRANSPORT("\tBAR%d: 0x%x\n", i, pci_header_regs[i+4]);
    }

    LOG_VIRTIO_TRANSPORT("\tCapabilities ptr: 0x%x\n", pci_header_regs[13] & 0xff);

    /* If the capability list bit is set, walk the cap list. */
    if (status & BIT(4)) {
        uint8_t cap_off = pci_header_regs[13] & 0xff;
        while (cap_off) {
            uint32_t virtio_cap_arr[4];
            virtio_cap_arr[0] = pci_read_32(bus, dev, func, cap_off);
            virtio_cap_arr[1] = pci_read_32(bus, dev, func, cap_off + 4);
            virtio_cap_arr[2] = pci_read_32(bus, dev, func, cap_off + 8);
            virtio_cap_arr[3] = pci_read_32(bus, dev, func, cap_off + 12);

            virtio_pci_cap_t *cap = (virtio_pci_cap_t *) virtio_cap_arr;

            if (cap->cap_vndr == PCI_CAP_ID_VNDR) {
                LOG_VIRTIO_TRANSPORT("\tCap @ 0x%x, vendor 0x%x\n", cap_off, cap->cap_vndr);
                LOG_VIRTIO_TRANSPORT("\t\tCap next: 0x%x\n", cap->cap_next);
                LOG_VIRTIO_TRANSPORT("\t\tCap len: 0x%x\n", cap->cap_len);
                LOG_VIRTIO_TRANSPORT("\t\tType: 0x%x\n", cap->cfg_type);
                LOG_VIRTIO_TRANSPORT("\t\tBar: 0x%x\n", cap->bar);
                LOG_VIRTIO_TRANSPORT("\t\tID: 0x%x\n", cap->id);
                LOG_VIRTIO_TRANSPORT("\t\tBar off: 0x%x\n", cap->offset);
                LOG_VIRTIO_TRANSPORT("\t\tBar Len: 0x%x\n", cap->length);
    
                // @billn break this out, this debug print functions mustn't have side effects
                if (cap->cfg_type == VIRTIO_PCI_CAP_NOTIFY_CFG) {
                    // 4.1.4.4 Notification structure layout
                    nftn_multiplier = pci_read_32(bus, dev, func, cap_off + sizeof(virtio_pci_cap_t));
                    LOG_VIRTIO_TRANSPORT("\t\tfuck 0x%x\n", nftn_multiplier);
                }
            }

            cap_off = cap->cap_next;
        }
    }
}

bool virtio_transport_probe(device_resources_t *device_resources, virtio_device_handle_t *device_handle_ret)
{
    assert(device_resources_check_magic(device_resources));
    // assert(device_resources->num_irqs == 1);
    // assert(device_resources->num_regions == 2);


    pci_debug_print_header(0, 2, 0);

    return true;
}

void *virtio_transport_get_device_config(virtio_device_handle_t *device_handle)
{
    return (void *) VADDR_DEVICE;
}

void virtio_transport_set_status(virtio_device_handle_t *device_handle, uint8_t status)
{
    get_cfg(device_handle->device_resources)->device_status = status;
}

uint8_t virtio_transport_get_status(virtio_device_handle_t *device_handle) {
    return get_cfg(device_handle->device_resources)->device_status;
}

uint32_t virtio_transport_get_device_features(virtio_device_handle_t *device_handle, uint32_t select)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle->device_resources);
    cfg->device_feature_select = select;
    return cfg->device_feature;
}

uint32_t virtio_transport_get_driver_features(virtio_device_handle_t *device_handle, uint32_t select)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle->device_resources);
    cfg->driver_feature_select = select;
    return cfg->driver_feature;
}

void virtio_transport_set_driver_features(virtio_device_handle_t *device_handle, uint32_t select, uint32_t driver_features)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle->device_resources);
    cfg->driver_feature_select = select;
    cfg->driver_feature = driver_features;
}

bool virtio_transport_queue_setup(virtio_device_handle_t *device_handle, uint32_t select, uint16_t size, uint64_t desc, uint64_t driver, uint64_t device)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle->device_resources);

    cfg->queue_select = select;
    cfg->queue_size = size;
    cfg->queue_desc = desc;
    cfg->queue_driver = driver;
    cfg->queue_device = device;
    cfg->queue_enable = 1;

    return true;
}

void virtio_transport_queue_notify(virtio_device_handle_t *device_handle, uint32_t select)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle->device_resources);

    cfg->queue_select = select;
    uint16_t q_off = cfg->queue_notify_off;
    uint16_t *addr = (uint16_t *)(VADDR_NOTIFY + (q_off * nftn_multiplier));
    *addr = (uint16_t) select;
}

uint32_t virtio_transport_read_isr(virtio_device_handle_t *device_handle)
{
    uint8_t *isr_ptr = (uint8_t *) VADDR_ISR;
    return (*isr_ptr);
}

void virtio_transport_write_isr(virtio_device_handle_t *device_handle, uint32_t isr)
{
    uint8_t *isr_ptr = (uint8_t *) VADDR_ISR;
    *isr_ptr = (uint8_t) isr;
}
