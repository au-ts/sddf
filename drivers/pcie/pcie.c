/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <string.h>
#include <microkit.h>
#include <os/sddf.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>

#include "pcie.h"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".ecam_configs"))) pci_ecam_config_t pci_ecam_config;

// regions[1..] are used for MSI-X BARs
uint8_t avail_region_idx = 1;

/**
 * Look for the capability of a device by ID
 * */
static struct shared_pci_cap *find_pci_cap_by_id(struct pci_config_space *config_space, uint8_t cap_id)
{
    struct shared_pci_cap *cap = (struct shared_pci_cap *)((uintptr_t)config_space + config_space->cap_ptr);
    while (cap != (struct shared_pci_cap *)config_space) {
        if (cap->cap_id == cap_id) {
            return cap;
        }
        cap = (struct shared_pci_cap *)((uintptr_t)config_space + cap->next_ptr);
    }
    return NULL;
}

void configure_pci_bar(struct pci_config_space *pci_header, uint8_t bar_id, pci_bar_t pci_bar_cfg)
{
    sddf_dprintf("bar_id: %d, base_addr: 0x%lx\n", bar_id, pci_bar_cfg.base_addr);
    if (pci_bar_cfg.base_addr) {
        volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + (bar_id * 0x04));
        // TODO: check if the BAR type is matched
        sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
        *mem_bar = 0xFFFFFFFF;
        // TODO:  read the size back written by the device
        sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
        *mem_bar = (uint32_t)pci_bar_cfg.base_addr;
        sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
    }
}

void configure_irqs(struct pci_config_space *pci_header, config_request_t config_request)
{
    bool ioapic_enabled = true;
    for (int i = 0; i < config_request.num_irqs; i++) {
        if (config_request.irqs[i].kind != irq_ioapic) {
            ioapic_enabled = false;
        }

        if (!ioapic_enabled && config_request.irqs[i].kind == irq_ioapic) {
            sddf_dprintf("error: I/O APIC can not be enabled with MSI/MSI-X\n");
            return;
        }
    }

    // Enable/Disable I/O APIC interrupts
    if (ioapic_enabled) {
        pci_header->command &= (~BIT(10));
    } else {
        pci_header->command |= BIT(10);
    }

    for (int i = 0; i < config_request.num_irqs; i++) {
        switch (config_request.irqs[i].kind) {
            case irq_ioapic: {
                // TODO: figure out how to reconfigure interrupt vectors
                break;
            };
            case irq_msi: {
                // TODO: configure MSI interrupts
                break;
            };
            case irq_msix: {
                struct msix_capability *msix_cap = (struct msix_capability *)find_pci_cap_by_id(pci_header, PCI_CAP_ID_MSIX);
                if (msix_cap) {
                    // Bits 2-0 refer to BAR ID
                    uint8_t bar_id = msix_cap->table_offset_bir & 0x5;
                    pci_bar_t msix_bar;
                    msix_bar.bar_id = bar_id;
                    msix_bar.base_addr = device_resources.regions[avail_region_idx].io_addr;
                    msix_bar.mem_mapped = true;

                    configure_pci_bar(pci_header, bar_id, msix_bar);

                    // Enable MSI-X
                    struct msix_msg_ctrl *msg_ctrl = &msix_cap->msg_ctrl;
                    msg_ctrl->msix_enable = 1;
                    sddf_dprintf("Table Size: 0x%x\n", msg_ctrl->table_size + 1);
                    sddf_dprintf("Function Mask: 0x%x\n", msg_ctrl->func_mask);
                    sddf_dprintf("MSI-X Enable: 0x%x\n", msg_ctrl->msix_enable);

                    struct msix_table *msix_table = (struct msix_table *)device_resources.regions[avail_region_idx].region.vaddr;
                    msix_table->msg_addr_low = 0xFEEu << 20;
                    msix_table->msg_data = 0x4030 + config_request.irqs[i].vector;
                    msix_table->vec_ctrl = 0x0;
                    sddf_dprintf("Vector 0 Message Addr Low: 0x%x\n", msix_table->msg_addr_low);
                    sddf_dprintf("Vector 0 Message Addr Hi: 0x%x\n", msix_table->msg_addr_hi);
                    sddf_dprintf("Vector 0 Message Data: 0x%x\n", msix_table->msg_data);
                    sddf_dprintf("Vector 0 Vector Control: 0x%x\n", msix_table->vec_ctrl);

                    uint32_t *msix_pba = (uint32_t *)(device_resources.regions[avail_region_idx].region.vaddr + 0x800);
                    sddf_dprintf("PBA: 0x%x\n", msix_pba[0]);

                    avail_region_idx += 1;
                } else {
                    sddf_dprintf("error: device does not support MSI-X\n");
                }
                break;
            };
        }

    }
}

void pci_bus_scan(uintptr_t bus_base)
{
    /* uint8_t pci_bus = (((uintptr_t)bus_base >> 20) & 0xff); */
    for (uint8_t pci_dev = 0; pci_dev < 32; pci_dev++) {
        for (uint8_t pci_func = 0; pci_func < 8; pci_func++) {
            struct pci_config_space *pci_header = (struct pci_config_space *)(bus_base + (pci_dev << 15) + (pci_func << 12));
            if (pci_header->vendor_id != 0xffff && pci_header->vendor_id != 0x0000) {
                sddf_dprintf("bus: 0x%lx, dev: 0x%lx, func: 0x%lx, vedor_id: 0x%x, device_id: 0x%x\n",
                             (((uintptr_t)pci_header >> 20) & 0xff),
                             (((uintptr_t)pci_header >> 15) & 0x1f),
                             (((uintptr_t)pci_header >> 12) & 0x7),
                             pci_header->vendor_id,
                             pci_header->device_id);

                /* for (int j = 0; j < 64; j++) { */
                /*     if (j && j % 16 == 0) sddf_dprintf("\n"); */
                /*     sddf_dprintf("%02x ", *(uint8_t *)(bus_base + (pci_dev << 15) + (pci_func << 12) + j)); */
                /* } */
                /* sddf_dprintf("\n"); */

                for (int i = 0; i < pci_ecam_config.num_requests; i++) {
                    config_request_t config_request = pci_ecam_config.requests[i];
                    sddf_dprintf("bus: 0x%x, dev: 0x%x, func: 0x%x\n", config_request.bus, config_request.dev, config_request.func);
                    if (config_request.device_id == pci_header->device_id && config_request.vendor_id == pci_header->vendor_id) {
                        sddf_dprintf("interrupt_line: 0x%x\n", pci_header->interrupt_line);
                        sddf_dprintf("interrupt_pin: 0x%x\n", pci_header->interrupt_pin);
                        for (int bar_id = 0; bar_id < PCI_DEV_MAX_BARS; bar_id++) {
                            configure_pci_bar(pci_header, bar_id, config_request.bars[bar_id]);

                            // TODO:  consider 64-bit memory

                        }
                        for (int j = 0; j < 256; j++) {
                            if (j && j % 16 == 0) sddf_dprintf("\n");
                            sddf_dprintf("%02x ", *(uint8_t *)(bus_base + (pci_dev << 15) + (pci_func << 12) + j));
                        }
                        sddf_dprintf("\n");

                        configure_irqs(pci_header, config_request);
                    }
                }
            }
        }
    }
}

void pci_ecam_scan(uintptr_t ecam_base, uint8_t start_bus, uint8_t end_bus)
{
    for (int i = start_bus; i <= end_bus; i++) {
        pci_bus_scan(ecam_base + (i << 20));
    }
}

void init(void)
{
    sddf_dprintf("PCIE|INFO: hello\n");
    sddf_dprintf("number of ECAMs: %d\n", device_resources.num_regions);
    sddf_dprintf("ecam_base: 0x%lx\n", (uintptr_t)(device_resources.regions[0].region.vaddr));
    sddf_dprintf("ecam_size: 0x%lx\n", device_resources.regions[0].region.size);


    uint16_t end_bus = device_resources.regions[0].region.size / BIT(20) - 1;
    sddf_dprintf("BIT(20): 0x%lx, end_bus: %d\n", BIT(20), end_bus);
    pci_ecam_scan((uintptr_t)device_resources.regions[0].region.vaddr, 0, end_bus);
}

void notified(sddf_channel ch)
{

}
