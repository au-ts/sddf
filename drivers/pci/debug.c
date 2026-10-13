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

const char *pci_class_and_subclass_to_string(uint8_t class, uint8_t subclass)
{
    // see https://admin.pci-ids.ucw.cz/read/PD/
    switch (class) {
    case 0x00:
        switch (subclass) {
        case 0x00:
            return "Non-VGA-Compatible Unclassified Device";
        case 0x01:
            return "VGA-Compatible Unclassified Device";
        }
        break;
    case 0x01:
        switch (subclass) {
        case 0x00:
            return "SCSI Bus Controller";
        case 0x01:
            return "IDE Controller";
        case 0x02:
            return "Floppy Disk Controller";
        case 0x03:
            return "IPI Bus Controller";
        case 0x04:
            return "RAID Controller";
        case 0x05:
            return "ATA Controller";
        case 0x06:
            return "Serial ATA Controller";
        case 0x07:
            return "Serial Attached SCSI Controller";
        case 0x08:
            return "Non-Volatile Memory Controller";
        case 0x09:
            return "Universal Flash Storage Controller";
        case 0x80:
            return "Other Mass Storage Controller";
        }
        break;
    case 0x02:
        switch (subclass) {
        case 0x00:
            return "Ethernet Controller";
        case 0x01:
            return "Token Ring Controller";
        case 0x02:
            return "FDDI Controller";
        case 0x03:
            return "ATM Controller";
        case 0x04:
            return "ISDN Controller";
        case 0x05:
            return "WorldFip Controller";
        case 0x06:
            return "PICMG 2.14 Multi Computing Controller";
        case 0x07:
            return "InfiniBand Controller";
        case 0x08:
            return "Fabric Controller";
        case 0x80:
            return "Other Network Controller";
        }
        break;
    case 0x03:
        switch (subclass) {
        case 0x00:
            return "VGA Compatible Controller";
        case 0x01:
            return "XGA Controller";
        case 0x02:
            return "3D Controller (Not VGA-Compatible)";
        case 0x80:
            return "Other Display Controller";
        }
        break;
    case 0x04:
        switch (subclass) {
        case 0x00:
            return "Multimedia Video Controller";
        case 0x01:
            return "Multimedia Audio Controller";
        case 0x02:
            return "Computer Telephony Device";
        case 0x03:
            return "Audio Device";
        case 0x80:
            return "Other Multimedia Controller";
        }
        break;
    case 0x05:
        switch (subclass) {
        case 0x00:
            return "RAM Controller";
        case 0x01:
            return "Flash Controller";
        case 0x02:
            return "CXL Memory Device";
        case 0x80:
            return "Other Memory Controller";
        }
        break;
    case 0x06:
        switch (subclass) {
        case 0x00:
            return "Host Bridge";
        case 0x01:
            return "ISA Bridge";
        case 0x02:
            return "EISA Bridge";
        case 0x03:
            return "MCA Bridge";
        case 0x04:
            return "PCI-to-PCI Bridge";
        case 0x05:
            return "PCMCIA Bridge";
        case 0x06:
            return "NuBus Bridge";
        case 0x07:
            return "CardBus Bridge";
        case 0x08:
            return "RACEway Bridge";
        case 0x09:
            return "Semi-Transparent PCI-to-PCI Bridge";
        case 0x0A:
            return "InfiniBand-to-PCI Host Bridge";
        case 0x0B:
            return "Advanced Switching to PCI Host Bridge";
        case 0x80:
            return "Other Bridge";
        }
        break;
    case 0x07:
        switch (subclass) {
        case 0x00:
            return "Serial Controller";
        case 0x01:
            return "Parallel Controller";
        case 0x02:
            return "Multiport Serial Controller";
        case 0x03:
            return "Modem";
        case 0x04:
            return "IEEE 488.1/2 (GPIB) Controller";
        case 0x05:
            return "Smart Card Controller";
        case 0x80:
            return "Other Simple Communication Controller";
        }
        break;
    case 0x08:
        switch (subclass) {
        case 0x00:
            return "PIC";
        case 0x01:
            return "DMA Controller";
        case 0x02:
            return "Timer";
        case 0x03:
            return "RTC Controller";
        case 0x04:
            return "PCI Hot-Plug Controller";
        case 0x05:
            return "SD Host Controller";
        case 0x06:
            return "IOMMU";
        case 0x07:
            return "Root Complex Event Collector";
        case 0x80:
            return "Other Base System Peripheral";
        }
        break;
    case 0x09:
        switch (subclass) {
        case 0x00:
            return "Keyboard Controller";
        case 0x01:
            return "Digitizer Pen";
        case 0x02:
            return "Mouse Controller";
        case 0x03:
            return "Scanner Controller";
        case 0x04:
            return "Gameport Controller";
        case 0x80:
            return "Other Input Device Controller";
        }
        break;
    case 0x0A:
        switch (subclass) {
        case 0x00:
            return "Generic Docking Station";
        case 0x80:
            return "Other Docking Station";
        }
        break;
    case 0x0B:
        switch (subclass) {
        case 0x00:
            return "386 Processor";
        case 0x01:
            return "486 Processor";
        case 0x02:
            return "Pentium Processor";
        case 0x03:
            return "Pentium Pro Processor";
        case 0x10:
            return "Alpha Processor";
        case 0x20:
            return "PowerPC Processor";
        case 0x30:
            return "MIPS Processor";
        case 0x40:
            return "Co-Processor";
        case 0x80:
            return "Other Processor";
        }
        break;
    case 0x0C:
        switch (subclass) {
        case 0x00:
            return "FireWire (IEEE 1394) Controller";
        case 0x01:
            return "ACCESS Bus Controller";
        case 0x02:
            return "SSA Controller";
        case 0x03:
            return "USB Controller";
        case 0x04:
            return "Fibre Channel Controller";
        case 0x05:
            return "SMBus Controller";
        case 0x06:
            return "InfiniBand Controller";
        case 0x07:
            return "IPMI Interface";
        case 0x08:
            return "SERCOS Interface (IEC 61491)";
        case 0x09:
            return "CANbus Controller";
        case 0x0A:
            return "MIPI I3C Host Controller";
        case 0x80:
            return "Other Serial Bus Controller";
        }
        break;
    case 0x0D:
        switch (subclass) {
        case 0x00:
            return "iRDA Compatible Controller";
        case 0x01:
            return "Consumer IR Controller";
        case 0x10:
            return "RF Controller";
        case 0x11:
            return "Bluetooth Controller";
        case 0x12:
            return "Broadband Controller";
        case 0x20:
            return "Ethernet Controller (802.11a)";
        case 0x21:
            return "Ethernet Controller (802.11b)";
        case 0x40:
            return "Cellular Controller/Modem";
        case 0x41:
            return "Cellular Controller/Modem plus Ethernet (802.11)";
        case 0x80:
            return "Other Wireless Controller";
        }
        break;
    case 0x0E:
        switch (subclass) {
        case 0x00:
            return "I2O Controller";
        }
        break;
    case 0x0F:
        switch (subclass) {
        case 0x01:
            return "Satellite TV Controller";
        case 0x02:
            return "Satellite Audio Controller";
        case 0x03:
            return "Satellite Voice Controller";
        case 0x04:
            return "Satellite Data Controller";
        }
        break;
    case 0x10:
        switch (subclass) {
        case 0x00:
            return "Network and Computing Encryption/Decryption Controller";
        case 0x10:
            return "Entertainment Encryption/Decryption Controller";
        case 0x80:
            return "Other Encryption Controller";
        }
        break;
    case 0x11:
        switch (subclass) {
        case 0x00:
            return "DPIO Module";
        case 0x01:
            return "Performance Counters";
        case 0x10:
            return "Communication Synchronizer";
        case 0x20:
            return "Signal Processing Management";
        case 0x80:
            return "Other Signal Processing Controller";
        }
        break;
    case 0x12:
        switch (subclass) {
        case 0x00:
            return "Processing Accelerator";
        case 0x01:
            return "SNIA SDXI Controller";
        }
        break;
    case 0x13:
        switch (subclass) {
        case 0x00:
            return "Non-Essential Instrumentation";
        }
        break;
    }

    return "Unknown";
}

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
        DEBUG_DRIVER("\t%lu: segment %u, start bus %u\n", i, pci_hb->segment, pci_hb->root_bus);

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
                     mcfg_entry->start_bus, mcfg_entry->end_bus_inclusive, mcfg_entry->paddr);
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