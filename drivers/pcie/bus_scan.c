/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <microkit.h>
#include <sddf/acpi/handover.h>

#include "internal.h"

#define PCI_MAX_NUM_RESOURCES_PER_BRIDGE ACPI_MAX_NUM_CRS_PER_HOST_BRIDGE

typedef struct {
    pci_path_t path;
    size_t num_resources;
    resource_range_t resources[PCI_MAX_NUM_RESOURCES_PER_BRIDGE];
} bus_scan_state_t;

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

static bool mem_bar_in_valid_aperature(uint64_t paddr, uint64_t size_bytes, bus_scan_state_t *scan_state)
{
    assert(size_bytes);
    for (int i = 0; i < scan_state->num_resources; i++) {
        resource_range_t *res = &scan_state->resources[i];
        if (res->kind == CRS_KIND_MEMORY) {
            if (paddr >= res->base && (paddr + size_bytes - 1) <= res->end_inclusive) {
                return true;
            }
        }
    }
    return false;
}

static void pcie_endpoint_bar_scan(pcie_drv_state_t *driver_state, volatile pci_conf_space_endpoint_t *endpoint_cs,
                                   pcie_function_t *pcie_func, bus_scan_state_t *scan_state)
{
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

        /* Read size, general procedure is write all 1s to BAR, read back the mask,
         * invert it, then restore the original value. This is why we want to disable I/O and mem space
         * decoding. So the device doesn't decode paddr 0xffffffff. */
        uint32_t lo_rb = 0;
        /* For 32-bit BAR: pretend the high half read back all ones (i.e. "nothing here" in PCI) */
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

        if (!mem_bar_in_valid_aperature(paddr, bar_size_bytes, scan_state)) {
            DEBUG_DRIVER_ERR("\t\t\tBAR not allocated by firmware\n");
        }

        pcie_func->bars[i].valid = true;
        pcie_func->bars[i].paddr = paddr;
        pcie_func->bars[i].size_bytes = bar_size_bytes;
        pcie_func->bars[i].prefetchable = prefetchable;

    read_bar_complete:
        endpoint_cs->hdr.command = orig_cmd;
        if (is_64_bit) {
            i++;
        }
    }
}

static bool handle_pcie_endpoint(pcie_drv_state_t *driver_state, host_bridge_t *hb,
                                 volatile pci_conf_space_endpoint_t *endpoint_cs, uint8_t bus, uint8_t dev,
                                 uint8_t func, bus_scan_state_t scan_state)
{
    if (driver_state->num_funcs == MAX_NUM_PCIE_FUNCTIONS) {
        DEBUG_DRIVER_ERR("out of memory to bookkeep PCIe functions, consider increasing MAX_NUM_PCIE_FUNCTIONS\n");
        return false;
    }

    pcie_function_t *pcie_func = &driver_state->funcs_table[driver_state->num_funcs];
    memset(pcie_func, 0, sizeof(pcie_function_t));
    pcie_func->owner = PCIE_FUNC_OWNER_NONE;

    pcie_func->bus = bus;
    pcie_func->dev = dev;
    pcie_func->func = func;
    pcie_func->path = scan_state.path;
    pcie_func->hb = hb;
    pcie_func->cs = endpoint_cs;

    if (endpoint_cs->interrupt_pin) {
        /* -1 to match ACPI PRT's 0-indexing */
        uint8_t int_pin = endpoint_cs->interrupt_pin - 1;
        prt_entry_t *prt = intx_to_prt(hb, scan_state.path, dev, int_pin);
        if (!prt) {
            return false;
        }

        DEBUG_DRIVER("\t\tInterrupt Pin: %u, GSI: %u\n", int_pin, prt->gsi);
        pcie_func->gsi = prt->gsi;
    }

    pcie_endpoint_bar_scan(driver_state, endpoint_cs, pcie_func, &scan_state);

    driver_state->num_funcs += 1;
    return true;
}

static bool bus_scan_recursive(pcie_drv_state_t *driver_state, host_bridge_t *hb, void *ecam, uint8_t bus,
                               bus_scan_state_t scan_state);

static bool handle_pcie_bridge(pcie_drv_state_t *driver_state, host_bridge_t *hb, void *ecam,
                               volatile pci_conf_space_bridge_t *bridge_cs, uint8_t bus, uint8_t dev, uint8_t func,
                               bus_scan_state_t scan_state)
{
    /* Bus number directly behind this bridge */
    uint8_t secondary = bridge_cs->secondary_bus_num;
    /* Highest bus number anywhere behind this bridge, i.e. could be behind a bridge in this bridge */
    uint8_t subordinate = bridge_cs->subordinate_bus_num;
    /* Check to prevent loops and rescans, the convention is that bus numbers will strictly increase down each path. */
    if (secondary > bus && secondary <= subordinate) {
        if (scan_state.path.depth == PCI_MAX_PATH_DEPTH - 1) {
            DEBUG_DRIVER_ERR("topology too deep, consider increasing PCI_MAX_PATH_DEPTH\n");
            return false;
        }

        bus_scan_state_t new_scan_state;
        memset(&new_scan_state, 0, sizeof(new_scan_state));
        new_scan_state.path = scan_state.path;
        new_scan_state.path.devfn[new_scan_state.path.depth++] = (dev << 3) | func;

        /* Get the memory aperatures of this bridge. See "3.2.5.8. Memory Base Register and Memory Limit Register"
         * of the "PCI-to-PCI Bridge Architecture Specification Revision 1.1" for more details. */
        uint32_t mem_base = bridge_cs->mem_base;
        mem_base = mem_base >> 4;
        mem_base = mem_base << 20;

        uint32_t mem_limit = bridge_cs->mem_limit;
        mem_limit = mem_limit >> 4;
        mem_limit = (mem_limit << 20) | 0xFFFFF; /* The register give the start of the last 1MiB block */

        if (mem_base < mem_limit) {
            DEBUG_DRIVER("\t\tMemory aperature: 0x%x..0x%x\n", mem_base, mem_limit);
            /* assert here is sound, because a pci-pci bridge only have 2 memory apertures. */
            assert(new_scan_state.num_resources < PCI_MAX_NUM_RESOURCES_PER_BRIDGE);
            new_scan_state.resources[new_scan_state.num_resources].kind = CRS_KIND_MEMORY;
            new_scan_state.resources[new_scan_state.num_resources].base = mem_base;
            new_scan_state.resources[new_scan_state.num_resources].end_inclusive = mem_limit;
            new_scan_state.num_resources++;
        }

        uint64_t prefetch_mem_base = bridge_cs->pre_mem_base;
        bool prefetch_is_64b = (prefetch_mem_base & 0xF) == 0x1 ? true : false;
        prefetch_mem_base = prefetch_mem_base >> 4;
        prefetch_mem_base = prefetch_mem_base << 20;
        if (prefetch_is_64b) {
            prefetch_mem_base |= ((uint64_t)bridge_cs->pre_mem_base_upper) << 32;
        }

        uint64_t prefetch_mem_limit = bridge_cs->pre_mem_limit;
        prefetch_mem_limit = prefetch_mem_limit >> 4;
        prefetch_mem_limit = prefetch_mem_limit << 20;
        prefetch_mem_limit |= ((uint64_t)bridge_cs->pre_mem_limit_upper) << 32;
        prefetch_mem_limit |= 0xFFFFF; /* The register give the start of the last 1MiB block */

        if (prefetch_mem_base < prefetch_mem_limit) {
            DEBUG_DRIVER("\t\tPrefetchable Memory aperature: 0x%lx..0x%lx\n", prefetch_mem_base, prefetch_mem_limit);
            assert(new_scan_state.num_resources < PCI_MAX_NUM_RESOURCES_PER_BRIDGE);
            new_scan_state.resources[new_scan_state.num_resources].kind = CRS_KIND_MEMORY;
            new_scan_state.resources[new_scan_state.num_resources].base = prefetch_mem_base;
            new_scan_state.resources[new_scan_state.num_resources].end_inclusive = prefetch_mem_limit;
            new_scan_state.num_resources++;
        }

        if (!bus_scan_recursive(driver_state, hb, ecam, secondary, new_scan_state)) {
            return false;
        }
    } else {
        DEBUG_DRIVER_ERR("bridge %02x:%02x.%x unconfigured or misprogrammed by firmware\n", bus, dev, func);
        // @billn todo, assign bus number and whatnot
    }

    return true;
}

static bool bus_scan_recursive(pcie_drv_state_t *driver_state, host_bridge_t *hb, void *ecam, uint8_t bus,
                               bus_scan_state_t scan_state)
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
            if (hdr_type == PCI_HEADER_TYPE_ENDPOINT) {
                volatile pci_conf_space_endpoint_t *endpoint_cs = (pci_conf_space_endpoint_t *)common_hdr;
                if (!handle_pcie_endpoint(driver_state, hb, endpoint_cs, bus, dev, func, scan_state)) {
                    return false;
                }
            } else if (hdr_type == PCI_HEADER_TYPE_PCI_TO_PCI_BRIDGE) {
                volatile pci_conf_space_bridge_t *bridge_cs = (pci_conf_space_bridge_t *)common_hdr;
                if (!handle_pcie_bridge(driver_state, hb, ecam, bridge_cs, bus, dev, func, scan_state)) {
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

bool host_bridges_scan(pcie_drv_state_t *driver_state)
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

        bus_scan_state_t scan_state;
        memset(&scan_state, 0, sizeof(scan_state));
        memcpy(&scan_state.resources, &hb_desc->crs_entries, sizeof(resource_range_t) * hb_desc->num_crs_entries);
        scan_state.num_resources = hb_desc->num_crs_entries;

        if (!bus_scan_recursive(driver_state, hb_desc, ecam_vaddr, bus, scan_state)) {
            return false;
        }
    }

    return true;
}