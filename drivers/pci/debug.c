/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
// #include "pci.h"

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/acpi/handover.h>

#include "internal.h"

static const char *crs_kind_to_string(range_kind_t kind)
{
    switch (kind) {
    case CRS_KIND_MEMORY:
        return "memory";
    case CRS_KIND_IO:
        return "io";
    case CRS_KIND_BUS:
        return "bus";
    default:
        return "unknown";
    }
}

void dump_acpi_info(acpi_handover_t *post_acpi_handover)
{
    DEBUG_DRIVER("ACPI handover:\n");

    DEBUG_DRIVER("Shadow CNode:\n");
    size_t num_slots = 0;
    shadow_cap_t *caps = shadow_cnode_get_caps_table(&post_acpi_handover->shadow_cnode, &num_slots);
    for (size_t cslot = 0; cslot < num_slots; cslot++) {
        if (caps[cslot].type != CAP_TYPE_NONE) {
            DEBUG_DRIVER("\tSlot %lu: type '%s', base 0x%lx, end 0x%lx\n", cslot,
                         shadow_cap_type_to_string(caps[cslot].type), caps[cslot].base_paddr, caps[cslot].end_paddr);
        }
    }

    DEBUG_DRIVER("PCI Host Bridges:\n");
    for (size_t i = 0; i < post_acpi_handover->num_host_bridges; i++) {
        host_bridge_t *pci_hb = &post_acpi_handover->host_bridges[i];
        DEBUG_DRIVER("\t%lu: segment %lu, start bus %lu\n", i, pci_hb->segment, pci_hb->root_bus);

        DEBUG_DRIVER("\t\tCRS entries:\n");
        for (size_t c = 0; c < pci_hb->num_crs_entries; c++) {
            resource_range_t *crs = &pci_hb->crs_entries[c];
            DEBUG_DRIVER("\t\t\tkind '%s', base 0x%lx, end 0x%lx\n", crs_kind_to_string(crs->kind), crs->base,
                         crs->end_inclusive);
        }

        DEBUG_DRIVER("\t\tPRT entries:\n");
        for (size_t p = 0; p < pci_hb->num_prt_entries; p++) {
            prt_entry_t *prt = &pci_hb->prt_entries[p];

            DEBUG_DRIVER("\t\t\tslot %hu, pin %hu, lvl trig %hu, act low %hu, gsi %u\n", prt->dev, prt->pin,
                         prt->level_triggered, prt->active_low, prt->gsi);

            if (prt->bridge_path.depth) {
                DEBUG_DRIVER("\t\t\t\thops from host bridge\n");
                for (uint8_t d = 0; d < prt->bridge_path.depth; d++) {
                    uint8_t dev = prt->bridge_path.devfn[d] >> 3;
                    uint8_t fn = prt->bridge_path.devfn[d] & 0x7;
                    DEBUG_DRIVER("\t\t\t\t\tdev: %hu, fn: %hu\n", dev, fn);
                }
            }
        }
    }

    DEBUG_DRIVER("ACPI MCFG:\n");
    for (size_t i = 0; i < post_acpi_handover->num_mcfg_entries; i++) {
        mcfg_entry_t *mcfg_entry = &post_acpi_handover->mcfg_entries[i];
        DEBUG_DRIVER("\tsegment %u, start bus %hu, end bus %hu, paddr 0x%lx\n", mcfg_entry->segment,
                     mcfg_entry->start_bus, mcfg_entry->end_bus, mcfg_entry->paddr);
    }

    DEBUG_DRIVER("Requested ISA devices:\n");
    // @billn todo

    DEBUG_DRIVER("ACPI MADT Interrupt Source Overrides:\n");
    for (size_t i = 0; i < post_acpi_handover->num_madt_iso_entries; i++) {
        madt_iso_entry_t *iso = &post_acpi_handover->madt_iso_entries[i];
        DEBUG_DRIVER("\tbus %hu, source %hu, GSI %u, lvl trig %hu, act low %hu\n", iso->bus, iso->isa_irq, iso->gsi,
                     iso->level_triggered, iso->active_low);
    }

    DEBUG_DRIVER("ACPI MADT I/O APICs:\n");
    for (size_t i = 0; i < post_acpi_handover->num_madt_ioapics; i++) {
        DEBUG_DRIVER("\tioapic %lu, GSI base %u\n", i, post_acpi_handover->madt_ioapic_gsi_bases[i]);
    }

    DEBUG_DRIVER("HPET: %s\n", post_acpi_handover->has_hpet ? "yes:" : "no");
    if (post_acpi_handover->has_hpet) {
        DEBUG_DRIVER("\tpaddr 0x%lx, min period clock tick %hu\n", post_acpi_handover->hpet.paddr,
                     post_acpi_handover->hpet.min_clk_tick);
    }

    DEBUG_DRIVER("FADT:\n");
    DEBUG_DRIVER("\tMessage Signalled Interrupts: %s\n", post_acpi_handover->system_supports_msi ? "yes" : "no");
}