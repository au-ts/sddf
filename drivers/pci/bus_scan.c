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
#include "pci.h"

static bool pci_path_equal(const pci_path_t *a, const pci_path_t *b)
{
    if (a->depth != b->depth) {
        return false;
    }
    for (uint8_t i = 0; i < a->depth; i++) {
        if (a->devfn[i] != b->devfn[i]) {
            return false;
        }
    }
    return true;
}

/* This is part of the bread and butter of the PCIe driver. The device's configuration space
 * only tells software what INTx pin (A, B, C or D) it is using. Using the PCI Routing Tables
 * (PRTs) from the firmware DSDT/SSDTs, we must work out what Global System Interrupt (GSI)
 * the INTx pin of this particular device maps to. Then later the code will map the GSI into
 * an I/O APIC chip and pin.
 *
 * The device may be behind several bridges. A bridge only has four interrupt pins going up,
 * shared by everything below it, and it rotates them by slot so devices don't all pile onto
 * INTA: pin P of the device in slot S comes out of the bridge as pin (P + S) % 4. If a bridge
 * has no PRT, we apply this "swizzle" ourselves, then repeat the lookup with the bridge as
 * the device, one level up.
 *
 * `path` must contain the route from the host bridge to `dev`'s parent bridge. It doesn't need
 * bus numbers, as each hop's dev.fn is relative to the bus the previous hop leads to. `pin` is
 * 0-based (INTA = 0), unlike the 1-based Interrupt Pin register in configuration space.
 *
 * Returns the matching PRT entry (GSI, trigger and polarity) from all the PRTs recorded
 * against the host bridge by the ACPI driver, or NULL if the firmware didn't describe one.
 */
static prt_entry_t *intx_to_prt(host_bridge_t *hb, pci_path_t path, uint8_t dev, uint8_t pin)
{
    for (;;) {
        bool have_table = false;

        for (size_t i = 0; i < hb->num_prt_entries; i++) {
            prt_entry_t *e = &hb->prt_entries[i];
            if (!pci_path_equal(&e->bridge_path, &path)) {
                continue;
            }
            have_table = true;
            if (e->dev == dev && e->pin == pin) {
                return e;
            }
        }

        if (have_table) {
            uint8_t bridge = path.devfn[path.depth - 1];
            DEBUG_DRIVER_ERR("Firmware bug: _PRT of bridge %02x.%x (depth %u) has no entry for slot %u INT%c\n",
                             bridge >> 3, bridge & 0x7, path.depth, dev, 'A' + pin);
            return NULL;
        }
        if (path.depth == 0) {
            DEBUG_DRIVER_ERR("Firmware did not describe INTx routing: no _PRT on any bridge up to the host "
                             "bridge, can't route slot %u INT%c on the root bus. Probably MSI only?\n",
                             dev, 'A' + pin);
            return NULL;
        }

        /* no _PRT here: swizzle and treat the bridge as the device we are looking for itself */
        pin = (pin + dev) % 4;
        path.depth--;
        dev = path.devfn[path.depth] >> 3;
    }
}

static bool handle_pcie_endpoint(pci_drv_state_t *driver_state, host_bridge_t *hb,
                                 volatile pci_conf_space_endpoint_t *endpoint_cs, uint8_t bus, uint8_t dev,
                                 uint8_t func, pci_path_t path)
{
    if (endpoint_cs->interrupt_pin) {
        /* -1 to match ACPI PRT's 0-indexing */
        uint8_t int_pin = endpoint_cs->interrupt_pin - 1;
        prt_entry_t *prt = intx_to_prt(hb, path, dev, int_pin);
        if (!prt) {
            return false;
        }

        DEBUG_DRIVER("\t\tInterrupt Pin: %u, GSI: %u\n", int_pin, prt->gsi);
    }

    for (int i = 0; i < PCI_TYPE_0_NUM_BARS; i++) {
        /* Don't care about I/O Space, for now... */
        uint32_t orig_bar_value = endpoint_cs->bars[i];
        if (orig_bar_value & PCI_BAR_IO_SPACE_MASK) {
            continue;
        }

        /* From https://wiki.osdev.org/PCI:
        * "Before attempting to read the information about the BAR, make sure to disable
        *  both I/O and memory decode in the command byte. You can restore the original
        *  value after completing the BAR info read. This is needed as some devices are
        *  known to decode the write of all ones to the register as an (unintended) access."
        */
        uint16_t orig_cmd = endpoint_cs->hdr.command;
        endpoint_cs->hdr.command = orig_cmd & ~PCI_COMMAND_IO_SPACE_MASK & ~PCI_COMMAND_MEM_SPACE_MASK;

        uint32_t orig_bar_value_high = 0;
        bool is_64_bit = ((orig_bar_value >> 1) & 0x3) == 0x2;
        if (is_64_bit) {
            if (i == PCI_TYPE_0_NUM_BARS - 1) {
                DEBUG_DRIVER_ERR("Firmware bug: last BAR can't be 64-bit!\n");
                goto read_bar_complete;
            }
            orig_bar_value_high = endpoint_cs->bars[i + 1];
        }

        /* Read size */
        uint32_t lo_rb = 0;
        /* 32-bit BAR: pretend the high half read back all ones */
        uint32_t hi_rb = 0xffffffff;

        endpoint_cs->bars[i] = 0xffffffff;
        lo_rb = endpoint_cs->bars[i];
        endpoint_cs->bars[i] = orig_bar_value;

        if (is_64_bit) {
            endpoint_cs->bars[i + 1] = 0xffffffff;
            hi_rb = endpoint_cs->bars[i + 1];
            endpoint_cs->bars[i + 1] = orig_bar_value_high;
        }

        if ((lo_rb & PCI_BAR_ADDR_MASK) == 0 && (!is_64_bit || hi_rb == 0))
            /* BAR not implemented by device */
            goto read_bar_complete;

        uint64_t mask = ((uint64_t)hi_rb << 32) | (lo_rb & PCI_BAR_ADDR_MASK);
        uint64_t bar_size_bytes = ~mask + 1;

        uint64_t paddr = (orig_bar_value & PCI_BAR_ADDR_MASK) | (((uint64_t)orig_bar_value_high) << 32);
        bool prefetchable = orig_bar_value & PCI_BAR_PREFETCHABLE_MASK ? true : false;

        DEBUG_DRIVER("\t\tBAR %u: paddr 0x%lx, size: 0x%lx prefetchable: %s\n", i, paddr, bar_size_bytes,
                     prefetchable ? "yes" : "no");

    read_bar_complete:
        endpoint_cs->hdr.command = orig_cmd;
        if (is_64_bit) {
            i++;
        }
    }

    return true;
}

static bool bus_scan_recursive(pci_drv_state_t *driver_state, host_bridge_t *hb, void *ecam, uint8_t bus,
                               pci_path_t path);

static bool handle_pcie_bridge(pci_drv_state_t *driver_state, host_bridge_t *hb, void *ecam,
                               volatile pci_conf_space_bridge_t *bridge_cs, uint8_t bus, uint8_t dev, uint8_t func,
                               pci_path_t path)
{
    uint8_t secondary = bridge_cs->secondary_bus_num;
    uint8_t subordinate = bridge_cs->subordinate_bus_num;
    if (secondary > bus && secondary <= subordinate) {
        pci_path_t new_path = path;
        if (new_path.depth == PCI_MAX_PATH_DEPTH) {
            DEBUG_DRIVER_ERR("topology too deep, consider increasing PCI_MAX_PATH_DEPTH\n");
            return false;
        }

        new_path.devfn[new_path.depth++] = (dev << 3) | func;
        if (!bus_scan_recursive(driver_state, hb, ecam, secondary, new_path)) {
            return false;
        }
    } else {
        DEBUG_DRIVER_ERR("bridge %02x:%02x.%x unconfigured\n", bus, dev, func);
        // @billn todo, assign bus number and whatnot
    }

    return true;
}

static bool bus_scan_recursive(pci_drv_state_t *driver_state, host_bridge_t *hb, void *ecam, uint8_t bus,
                               pci_path_t path)
{
    for (uint8_t dev = 0; dev < BIT(PCI_DEV_BITS); dev++) {
        for (uint8_t func = 0; func < BIT(PCI_FUNC_BITS); func++) {
            volatile pci_conf_space_common_hdr_t *common_hdr = pci_geo_addr_to_conf_space(ecam, bus, dev, func);

            if (common_hdr->vendor_id == NO_VENDOR) {
                if (func == 0) {
                    /* nothing in this slot */
                    break;
                }
                /* gap in a multi-function device */
                continue;
            }

            DEBUG_DRIVER("\t%02x:%02x.%x:\n", bus, dev, func);
            DEBUG_DRIVER("\t\tVendor: 0x%04X, Device: 0x%04X\n", common_hdr->vendor_id, common_hdr->device_id);
            DEBUG_DRIVER("\t\tClass: %s\n",
                         pci_class_and_subclass_to_string(common_hdr->class_code, common_hdr->subclass));

            uint8_t hdr_type = common_hdr->header_type & 0x7f;
            if (hdr_type == 0) {
                volatile pci_conf_space_endpoint_t *endpoint_cs = (pci_conf_space_endpoint_t *)common_hdr;
                if (!handle_pcie_endpoint(driver_state, hb, endpoint_cs, bus, dev, func, path)) {
                    return false;
                }
            } else if (hdr_type == 1) {
                volatile pci_conf_space_bridge_t *bridge_cs = (pci_conf_space_bridge_t *)common_hdr;
                if (!handle_pcie_bridge(driver_state, hb, ecam, bridge_cs, bus, dev, func, path)) {
                    return false;
                }
            }

            if (func == 0 && !(common_hdr->header_type & 0x80))
                /* single-function device */
                break;
        }
    }

    return true;
}

bool host_bridges_scan(pci_drv_state_t *driver_state)
{
    for (size_t hb = 0; hb < driver_state->handover->num_host_bridges; hb++) {
        host_bridge_t *hb_desc = &driver_state->handover->host_bridges[hb];

        size_t ecam_idx;
        uint16_t segment = hb_desc->segment;
        uint8_t bus = hb_desc->root_bus;
        if (!bus_and_segment_to_ecam_idx(driver_state, segment, bus, &ecam_idx)) {
            DEBUG_DRIVER_ERR("Firmware bug: failed to look up ECAM for host bridge with segment %u, root bus %u\n",
                             hb_desc->segment, hb_desc->root_bus);
            return false;
        }
        assert(ecam_idx <= driver_state->handover->num_mcfg_entries);
        void *ecam_vaddr = driver_state->ecams_vaddr[ecam_idx];

        DEBUG_DRIVER("Host bridge segment %u, root bus %u:\n", segment, bus);

        pci_path_t path = { .depth = 0 };
        if (!bus_scan_recursive(driver_state, hb_desc, ecam_vaddr, bus, path)) {
            return false;
        }
    }

    return true;
}