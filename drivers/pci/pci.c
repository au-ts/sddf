/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "pci.h"

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>

uintptr_t pci_resources_vaddr;
seL4_CPtr cnode_cptr_pci_resources;
pci_resources_t *pci_resources;

void init(void)
{
    sddf_dprintf("PCI driver\n");
    pci_resources = (pci_resources_t *)pci_resources_vaddr;
}

// TODO: pass bus start and end as arguments
void pci_bus_scan(uintptr_t bus_base)
{
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
            }
        }
    }
}

void notified(microkit_channel ch)
{
    sddf_dprintf("[PCI driver] notified by ch %d\n", ch);

    for (int i = 0; i < pci_resources->num_pci_groups; i++) {
        sddf_dprintf("PCI segment group: %u, base addr: 0x%lx, bus_range: [%u-%u]\n",
                     pci_resources->pci_seg_groups[i].group_id,
                     pci_resources->pci_seg_groups[i].base_addr,
                     pci_resources->pci_seg_groups[i].bus_start,
                     pci_resources->pci_seg_groups[i].bus_end);
        pci_bus_scan(pci_resources->pci_seg_groups[i].base_addr);
    }

    for (int i = 0; i < pci_resources->num_bridges; i++) {
        uint8_t num_res = pci_resources->bridges[i].num_dev_resources;
        sddf_dprintf("num_res: %u\n", num_res);
        for (int j = 0; j < num_res; j++) {
            device_resource_t *dev_res = (device_resource_t *)&pci_resources->bridges[i].dev_resources[j];
            sddf_dprintf("resource type: %u, min_addr: 0x%lx, max_addr: 0x%lx\n", dev_res->type, dev_res->min_addr, dev_res->max_addr);
        }
    }

    /* seL4_Error error = seL4_Untyped_Retype(cnode_cptr_pci_resources + 1, */
    /*                                        seL4_X86_LargePageObject, */
    /*                                        0, */
    /*                                        cnode_cptr_pci_resources, 0, 0, */
    /*                                        2, 1); */
    /* sddf_dprintf("error: %d\n", error); */
}
