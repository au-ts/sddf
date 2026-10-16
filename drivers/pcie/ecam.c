/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <microkit.h>
#include <sddf/acpi/handover.h>
#include <sddf/util/printf.h>
#include <sddf/util/vspace.h>

#include "internal.h"

bool map_ecams(pcie_drv_state_t *driver_state)
{
    assert(driver_state->handover->num_mcfg_entries <= ACPI_MAX_NUM_MCFG_ENTRIES);
    for (size_t i = 0; i < driver_state->handover->num_mcfg_entries; i++) {
        mcfg_entry_t *mcfg_entry = &driver_state->handover->mcfg_entries[i];

        /* The paddr in the MCFG is not the real base, it starts from bus 0,
         * not mcfg_entry->start_bus, so we need to correct for this */
        uint64_t actual_paddr = mcfg_entry->paddr + ((uint64_t)mcfg_entry->start_bus << 20);
        uint64_t ecam_size_bytes = ((mcfg_entry->end_bus_inclusive + 1) - mcfg_entry->start_bus)
                                 * PCIE_SIZE_BYTES_PER_BUS;
        ecam_size_bytes = ROUND_UP(ecam_size_bytes, BIT(seL4_LargePageBits));

        void *vaddr = (void *)driver_state->vaddr_watermark;

        DEBUG_DRIVER("mapping ECAM for segment %u, start bus %u, end bus %u, paddr 0x%lx, at vaddr 0x%lx, with size "
                     "bytes 0x%lx\n",
                     mcfg_entry->segment, mcfg_entry->start_bus, mcfg_entry->end_bus_inclusive, mcfg_entry->paddr,
                     (uintptr_t)vaddr, ecam_size_bytes);

        if (!map_memory_region(&driver_state->handover->shadow_cnode, CPTR_SELF_VSPACE, actual_paddr, ecam_size_bytes,
                               true, (uintptr_t)vaddr, seL4_ReadWrite, seL4_X86_CacheDisabled)) {
            DEBUG_DRIVER_ERR("mapping unsuccessful\n");
            return false;
        }

        driver_state->ecams_vaddr[i] = vaddr - (mcfg_entry->start_bus * PCIE_SIZE_BYTES_PER_BUS);
        driver_state->vaddr_watermark += ecam_size_bytes;
    }

    DEBUG_DRIVER("All ECAMs mapped\n");
    return true;
}

bool bus_and_segment_to_ecam_idx(pcie_drv_state_t *driver_state, uint16_t segment, uint8_t bus, size_t *idx)
{
    for (size_t i = 0; i < driver_state->handover->num_mcfg_entries; i++) {
        mcfg_entry_t *mcfg_entry = &driver_state->handover->mcfg_entries[i];
        if (mcfg_entry->segment == segment && bus >= mcfg_entry->start_bus && bus <= mcfg_entry->end_bus_inclusive) {
            *idx = i;
            return true;
        }
    }
    return false;
}

pci_conf_space_common_hdr_t *pci_geo_addr_to_conf_space(void *ecam, uint8_t bus, uint8_t dev, uint8_t func)
{
    uintptr_t ecam_base = (uintptr_t)ecam;
    uintptr_t conf_space = ecam_base + ((bus << 20) | (dev << 15) | (func << 12));
    return (pci_conf_space_common_hdr_t *)conf_space;
}
