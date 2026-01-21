/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <sddf/pci/conf_space.h>
#include <sddf/virtio/transport/common.h>
#include <sddf/virtio/transport/pci.h>
#include <sddf/resources/device.h>

#define DEVICE_REGS_COMMON 0x0
#define DEVICE_REGS_ISR 0x1
#define DEVICE_REGS_DEVICE 0x2
#define DEVICE_REGS_NOTIFY 0x3
#define DEVICE_REGS_REGION_SIZE 0x1000

#define PCI_ADDR_PORT_ID 1
#define PCI_ADDR_PORT_ADDR 0xCF8
#define PCI_DATA_PORT_ID 1
#define PCI_DATA_PORT_ADDR 0xCFC

/* Multiplier for virtIO queue kick mechanism. */
uint32_t nftn_multiplier;

uint32_t pci_compute_port_address(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off)
{
    uint32_t lbus = (uint32_t)bus;
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

// @billn should prolly use ecam instead of this io port business
uint32_t pci_x86_read_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off)
{
    uint32_t addr = pci_compute_port_address(bus, dev, func, off);

    /* Write the address into the "select" port, then the data will be available at the "data" port. */
    microkit_x86_ioport_write_32(PCI_ADDR_PORT_ID, PCI_ADDR_PORT_ADDR, addr);
    return microkit_x86_ioport_read_32(PCI_DATA_PORT_ID, PCI_DATA_PORT_ADDR);
}

void pci_x86_write_8(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off, uint8_t data)
{
    uint32_t addr = pci_compute_port_address(bus, dev, func, off);
    microkit_x86_ioport_write_32(PCI_ADDR_PORT_ID, PCI_ADDR_PORT_ADDR, addr);
    microkit_x86_ioport_write_8(PCI_DATA_PORT_ID, PCI_DATA_PORT_ADDR, data);
}

void pci_x86_write_16(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off, uint16_t data)
{
    uint32_t addr = pci_compute_port_address(bus, dev, func, off);
    microkit_x86_ioport_write_32(PCI_ADDR_PORT_ID, PCI_ADDR_PORT_ADDR, addr);
    microkit_x86_ioport_write_16(PCI_DATA_PORT_ID, PCI_DATA_PORT_ADDR, data);
}

void pci_x86_write_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off, uint32_t data)
{
    uint32_t addr = pci_compute_port_address(bus, dev, func, off);
    microkit_x86_ioport_write_32(PCI_ADDR_PORT_ID, PCI_ADDR_PORT_ADDR, addr);
    microkit_x86_ioport_write_32(PCI_DATA_PORT_ID, PCI_DATA_PORT_ADDR, data);
}

void *get_cfg(virtio_device_handle_t *device_handle, uint8_t cfg_type)
{
    return (void *)((uintptr_t)device_handle->device_resources->regions[0].region.vaddr + cfg_type * DEVICE_REGS_REGION_SIZE);
}

void pci_debug_print_header(uint8_t bus, uint8_t dev, uint8_t func, pci_gen_dev_hdr_t *pci_device_header)
{
    if (pci_device_header->common_hdr.header_type != PCI_HEADER_TYPE_GENERAL) {
        LOG_VIRTIO_TRANSPORT("printing non device pci header is unsupported.\n");
    }

    LOG_VIRTIO_TRANSPORT("BEGIN PCI DEVICE HEADER PRINTING:\n");
    LOG_VIRTIO_TRANSPORT("\tDevice ID: 0x%x\n", pci_device_header->common_hdr.device_id);
    LOG_VIRTIO_TRANSPORT("\tVendor ID: 0x%x\n", pci_device_header->common_hdr.vendor_id);
    LOG_VIRTIO_TRANSPORT("\tStatus: 0x%x\n", pci_device_header->common_hdr.status);
    LOG_VIRTIO_TRANSPORT("\tCommand: 0x%x\n", pci_device_header->common_hdr.command);
    LOG_VIRTIO_TRANSPORT("\tClass code: 0x%x\n", pci_device_header->common_hdr.class_code);
    LOG_VIRTIO_TRANSPORT("\tSubclass: 0x%x\n", pci_device_header->common_hdr.subclass);
    LOG_VIRTIO_TRANSPORT("\tProgramming Interface: 0x%x\n", pci_device_header->common_hdr.prog_if);
    LOG_VIRTIO_TRANSPORT("\tRevision ID: 0x%x\n", pci_device_header->common_hdr.rev_id);
    LOG_VIRTIO_TRANSPORT("\tBuilt-in Self Test: 0x%x\n", pci_device_header->common_hdr.bist);
    LOG_VIRTIO_TRANSPORT("\tHeader type: a general device\n");
    LOG_VIRTIO_TRANSPORT("\tLatency timer: 0x%x\n", pci_device_header->common_hdr.latency_timer);
    LOG_VIRTIO_TRANSPORT("\tCache line size: 0x%x\n", pci_device_header->common_hdr.cache_line_size);

    for (int i = 0; i < PCI_GEN_DEV_NUM_BARS; i++) {
        LOG_VIRTIO_TRANSPORT("\tBAR%d: 0x%x\n", i, pci_device_header->base_address_registers[i]);
    }

    LOG_VIRTIO_TRANSPORT("\tCapabilities ptr: 0x%x\n", pci_device_header->cap_ptr);

    /* If the capability list bit is set, walk the cap list. */
    if (pci_device_header->common_hdr.status & BIT(4)) {
        uint8_t cap_off = pci_device_header->cap_ptr;
        while (cap_off) {
            uint32_t virtio_cap_arr[4];
            virtio_cap_arr[0] = pci_x86_read_32(bus, dev, func, cap_off);
            virtio_cap_arr[1] = pci_x86_read_32(bus, dev, func, cap_off + 4);
            virtio_cap_arr[2] = pci_x86_read_32(bus, dev, func, cap_off + 8);
            virtio_cap_arr[3] = pci_x86_read_32(bus, dev, func, cap_off + 12);

            virtio_pci_cap_t *cap = (virtio_pci_cap_t *)virtio_cap_arr;

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
                    nftn_multiplier = pci_x86_read_32(bus, dev, func, cap_off + sizeof(virtio_pci_cap_t));
                    LOG_VIRTIO_TRANSPORT("\t\tnftn_multiplier: 0x%x\n", nftn_multiplier);
                }
            }

            cap_off = cap->cap_next;
        }
    }
}

static bool read_pci_general_device_header(uint8_t bus, uint8_t dev, uint8_t func, pci_gen_dev_hdr_t *ret)
{
    uint32_t pci_device_header[sizeof(pci_gen_dev_hdr_t) / sizeof(uint32_t)];

    /* Read the first 4 32-bits header registers to work out the header type. */
    int i = 0;
    for (; i < sizeof(pci_common_hdr_t) / sizeof(uint32_t); i++) {
        pci_device_header[i] = pci_x86_read_32(bus, dev, func, i * 4);
    }

    uint8_t hdr_type = (pci_device_header[3] >> 16) & 0xff;
    if (hdr_type != PCI_HEADER_TYPE_GENERAL) {
        LOG_VIRTIO_TRANSPORT("parsing non device pci header is currently unsupported.\n");
        return false;
    }

    /* Now read the rest of the header registers */
    for (; i < sizeof(pci_gen_dev_hdr_t) / sizeof(uint32_t); i++) {
        pci_device_header[i] = pci_x86_read_32(bus, dev, func, i * 4);
    }

    memcpy((uint8_t *)ret, (uint8_t *)pci_device_header, sizeof(pci_gen_dev_hdr_t));
    return true;
}

bool virtio_transport_probe(device_resources_t *device_resources, virtio_device_handle_t *device_handle_ret,
                            uint32_t device_id)
{
    assert(device_resources_check_magic(device_resources));

    uint8_t bus = device_handle_ret->pci_bus;
    uint8_t dev = device_handle_ret->pci_dev;
    uint8_t func = device_handle_ret->pci_func;
    device_handle_ret->device_resources = device_resources;

    pci_gen_dev_hdr_t pci_device_header;
    assert(read_pci_general_device_header(bus, dev, func, &pci_device_header));

    if (device_id == VIRTIO_DEVICE_ID_NET) {
        if (pci_device_header.common_hdr.class_code != PCI_CLASS_NETWORK_CONTROLLER) {
            LOG_VIRTIO_TRANSPORT("PCI device @ %u:%u.%u, with class code 0x%x is not a network controller!\n",
                                 pci_device_header.common_hdr.class_code, bus, dev, func);
            return false;
        }
        if (pci_device_header.common_hdr.subclass != PCI_CLASS_NETWORK_SUBCLASS_ETHERNET) {
            LOG_VIRTIO_TRANSPORT("PCI device @ %u:%u.%u, with subclass 0x%x is not an ethernet controller!\n",
                                 pci_device_header.common_hdr.subclass, bus, dev, func);
            return false;
        }
        if (pci_device_header.common_hdr.vendor_id != VIRTIO_PCI_VEN_ID) {
            LOG_VIRTIO_TRANSPORT("PCI device @ %u:%u.%u, with vendor id 0x%x isn't a virtio device!\n",
                                 pci_device_header.common_hdr.vendor_id, bus, dev, func);
            return false;
        }
        if (pci_device_header.common_hdr.device_id != VIRTIO_NET_PCI_DEV_ID) {
            LOG_VIRTIO_TRANSPORT("PCI device @ %u:%u.%u, with device id 0x%x isn't a virtio network device!\n",
                                 pci_device_header.common_hdr.device_id, bus, dev, func);
            return false;
        }
    } else if (device_id == VIRTIO_DEVICE_ID_BLK) {
        if (pci_device_header.common_hdr.class_code != PCI_CLASS_MASS_STORAGE_CONTROLLER) {
            LOG_VIRTIO_TRANSPORT("PCI device @ %u:%u.%u, with class code 0x%x is not a block controller!\n",
                                 pci_device_header.common_hdr.class_code, bus, dev, func);
            return false;
        }
        if (pci_device_header.common_hdr.subclass != PCI_CLASS_NETWORK_SUBCLASS_ETHERNET) {
            LOG_VIRTIO_TRANSPORT("PCI device @ %u:%u.%u, with subclass 0x%x is not an block controller!\n",
                                 pci_device_header.common_hdr.subclass, bus, dev, func);
            return false;
        }
        if (pci_device_header.common_hdr.vendor_id != VIRTIO_PCI_VEN_ID) {
            LOG_VIRTIO_TRANSPORT("PCI device @ %u:%u.%u, with vendor id 0x%x isn't a block device!\n",
                                 pci_device_header.common_hdr.vendor_id, bus, dev, func);
            return false;
        }
        if (pci_device_header.common_hdr.device_id != VIRTIO_BLK_PCI_DEV_ID) {
            LOG_VIRTIO_TRANSPORT("PCI device @ %u:%u.%u, with device id 0x%x isn't a virtio block device!\n",
                                 pci_device_header.common_hdr.device_id, bus, dev, func);
            return false;
        }
    } else {
        LOG_VIRTIO_TRANSPORT("Unknown or undefined device class for virtio PCI transport.\n");
    }

    pci_debug_print_header(bus, dev, func, &pci_device_header);

    return true;
}

void *virtio_transport_get_device_config(virtio_device_handle_t *device_handle)
{
    void *test_ptr = get_cfg(device_handle, DEVICE_REGS_DEVICE);
    for (int j = 0; j < 256; j++) {
        if (j && j % 16 == 0) sddf_dprintf("\n");
        sddf_dprintf("%02x ", *(uint8_t *)(test_ptr + j));
    }
    sddf_dprintf("\n");
    return get_cfg(device_handle, DEVICE_REGS_DEVICE);
}

void virtio_transport_set_status(virtio_device_handle_t *device_handle, uint8_t status)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle, DEVICE_REGS_COMMON);
    cfg->device_status = status;
}

uint8_t virtio_transport_get_status(virtio_device_handle_t *device_handle)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle, DEVICE_REGS_COMMON);
    return cfg->device_status;
}

uint32_t virtio_transport_get_device_features(virtio_device_handle_t *device_handle, uint32_t select)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle, DEVICE_REGS_COMMON);
    cfg->device_feature_select = select;
    return cfg->device_feature;
}

uint32_t virtio_transport_get_driver_features(virtio_device_handle_t *device_handle, uint32_t select)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle, DEVICE_REGS_COMMON);
    cfg->driver_feature_select = select;
    return cfg->driver_feature;
}

void virtio_transport_set_driver_features(virtio_device_handle_t *device_handle, uint32_t select,
                                          uint32_t driver_features)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle, DEVICE_REGS_COMMON);
    cfg->driver_feature_select = select;
    cfg->driver_feature = driver_features;
    cfg->config_msix_vector = 0;
}

bool virtio_transport_queue_setup(virtio_device_handle_t *device_handle, uint32_t select, uint16_t size, uint64_t desc,
                                  uint64_t driver, uint64_t device)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle, DEVICE_REGS_COMMON);

    cfg->queue_select = select;
    cfg->queue_msix_vector = 0;
    cfg->queue_size = size;
    cfg->queue_desc = desc;
    cfg->queue_driver = driver;
    cfg->queue_device = device;
    cfg->queue_enable = 1;

    return true;
}

void virtio_transport_queue_notify(virtio_device_handle_t *device_handle, uint32_t select)
{
    virtio_pci_common_cfg_t *cfg = get_cfg(device_handle, DEVICE_REGS_COMMON);

    cfg->queue_select = select;
    uint16_t q_off = cfg->queue_notify_off;
    uint16_t *addr = (uint16_t *)(get_cfg(device_handle, DEVICE_REGS_NOTIFY) + (uintptr_t)(q_off * nftn_multiplier));
    *addr = (uint16_t)select;
}

uint32_t virtio_transport_read_isr(virtio_device_handle_t *device_handle)
{
    uint8_t *isr_ptr = (uint8_t *)get_cfg(device_handle, DEVICE_REGS_ISR);
    return (*isr_ptr);
}

void virtio_transport_write_isr(virtio_device_handle_t *device_handle, uint32_t isr)
{
    uint8_t *isr_ptr = (uint8_t *)get_cfg(device_handle, DEVICE_REGS_ISR);
    *isr_ptr = (uint8_t)isr;
}
