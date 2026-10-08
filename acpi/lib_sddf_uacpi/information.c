/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include <uacpi/acpi.h>
#include <uacpi/tables.h>
#include <uacpi/context.h>
#include <uacpi/resources.h>
#include <uacpi/utilities.h>
#include <sddf/acpi/lib_sddf_uacpi.h>
#include <sddf/acpi/information.h>
#include <sddf/util/printf.h>
#include <sddf/util/shadow_cnode.h>
#include "logging.h"

/* Below 1 MiB is legacy: VGA (0xa0000-0xbffff), option ROMs and BIOS shadow (0xc0000-0xfffff) */
#define PCI_ALLOC_MIN_MEM  0x100000ULL

/* A bit ugly */
static acpi_handover_t *handover;

static char *address_common_type_to_string(uint8_t type)
{
    switch (type) {
    case UACPI_RANGE_MEMORY:
        return "memory";
    case UACPI_RANGE_IO:
        return "io";
    case UACPI_RANGE_BUS:
        return "bus";
    default:
        return "unknown";
    }
}

static char *crs_resource_type_to_string(uint32_t type)
{
    switch (type) {
    case UACPI_RESOURCE_TYPE_ADDRESS16:
        return "address 16";
    case UACPI_RESOURCE_TYPE_ADDRESS32:
        return "address 32";
    case UACPI_RESOURCE_TYPE_ADDRESS64:
        return "address 64";
    case UACPI_RESOURCE_TYPE_ADDRESS64_EXTENDED:
        return "address 64 ext";
    case UACPI_RESOURCE_TYPE_IO:
        return "address io";
    case UACPI_RESOURCE_TYPE_FIXED_IO:
        return "fixed io";
    case UACPI_RESOURCE_TYPE_END_TAG:
        return "end tag";
    default:
        return "unknown";
    }
}

static uacpi_iteration_decision crs_cb(void *ctx, uacpi_resource *res)
{
    uacpi_resource_address_common *common_desc;
    uint64_t granularity = 0, min = 0, max = 0, transl_off = 0, addr_len = 0, attr = 0;

    switch (res->type) {
    case UACPI_RESOURCE_TYPE_ADDRESS16:
        common_desc = &res->address16.common;
        granularity = res->address16.granularity;
        min = res->address16.minimum;
        max = res->address16.maximum;
        transl_off = res->address16.translation_offset;
        addr_len = res->address16.address_length;
        break;
    case UACPI_RESOURCE_TYPE_ADDRESS32:
        common_desc = &res->address32.common;
        granularity = res->address32.granularity;
        min = res->address32.minimum;
        max = res->address32.maximum;
        transl_off = res->address32.translation_offset;
        addr_len = res->address32.address_length;
        break;
    case UACPI_RESOURCE_TYPE_ADDRESS64:
        common_desc = &res->address64.common;
        granularity = res->address64.granularity;
        min = res->address64.minimum;
        max = res->address64.maximum;
        transl_off = res->address64.translation_offset;
        addr_len = res->address64.address_length;
        break;
    case UACPI_RESOURCE_TYPE_ADDRESS64_EXTENDED:
        common_desc = &res->address64_extended.common;
        granularity = res->address64_extended.granularity;
        min = res->address64_extended.minimum;
        max = res->address64_extended.maximum;
        transl_off = res->address64_extended.translation_offset;
        addr_len = res->address64_extended.address_length;
        attr = res->address64_extended.attributes;
        break;
    default:
        /* Not something we care about, e.g. end tag, io range, bus range etc */
        return UACPI_ITERATION_DECISION_CONTINUE;
    }

    if (common_desc->type == UACPI_RANGE_BUS) {
        DEBUG_ACPI("CRS bus entry 0x%lx..0x%lx\n", min, max);
        return UACPI_ITERATION_DECISION_CONTINUE;
    }

    if (!addr_len) {
        return UACPI_ITERATION_DECISION_CONTINUE;
        /* Only care about memory aperatures that are above the legacy stuff */
    } else if (common_desc->type != UACPI_RANGE_MEMORY) {
        return UACPI_ITERATION_DECISION_CONTINUE;
    } else if (max < PCI_ALLOC_MIN_MEM) {
        return UACPI_ITERATION_DECISION_CONTINUE;
    } else if (common_desc->direction == UACPI_CONSUMER) {
        /* Skip "consumer" ranges: those are used by the host bridge itself (e.g. its own
         * registers). We only want "producer" ranges, which it forwards to devices below it. */
        return UACPI_ITERATION_DECISION_CONTINUE;
    } else if ((max + 1) - min != addr_len) {
        DEBUG_ACPI_ERR("Firmware bug, bad CRS: (max + 1) - min != addr_len, (%lu + 1) - %lu != %lu, continuing\n", max,
                       min, addr_len);
        return UACPI_ITERATION_DECISION_CONTINUE;
    }

    size_t *num_crs_entry = &handover->host_bridges[handover->num_host_bridges].num_crs_entry;
    if (*num_crs_entry == ACPI_MAX_NUM_CRS_PER_HOST_BRIDGE) {
        DEBUG_ACPI_ERR("Max number of CRS entry reached for host bridge %zu, consider increasing "
                       "ACPI_MAX_NUM_CRS_PER_HOST_BRIDGE\n",
                       handover->num_host_bridges);
        return UACPI_ITERATION_DECISION_BREAK;
    }

    DEBUG_ACPI("CRS entry type '%s', address type '%s', granularity 0x%lx, min 0x%lx, max 0x%lx, translation off "
               "0x%lx, addr len 0x%lx, attr 0x%lx\n",
               crs_resource_type_to_string(res->type), address_common_type_to_string(common_desc->type), granularity,
               min, max, transl_off, addr_len, attr);

    crs_entry_t *cur_crs_entry = &handover->host_bridges[handover->num_host_bridges].crs_entries[*num_crs_entry];
    cur_crs_entry->base = min;
    cur_crs_entry->end = max;

    switch (common_desc->type) {
    case UACPI_RANGE_MEMORY:
        cur_crs_entry->kind = CRS_KIND_MEMORY;
        break;
    case UACPI_RANGE_IO:
        cur_crs_entry->kind = CRS_KIND_IO;
        break;
    case UACPI_RANGE_BUS:
        cur_crs_entry->kind = CRS_KIND_BUS;
        break;
    default:
        DEBUG_ACPI_ERR("oh no uACPI bug or wrong kind of type\n");
        assert(false);
    }

    (*num_crs_entry)++;

    return UACPI_ITERATION_DECISION_CONTINUE;
}

static uacpi_iteration_decision prt_cb(void *ctx, uacpi_namespace_node *node, uacpi_u32 depth)
{
    /* This is called every device node under the host bridge and parse their PRT if they have it. */
    uacpi_pci_routing_table *prt;
    uacpi_status st = uacpi_get_pci_routing_table(node, &prt);

    if (st == UACPI_STATUS_NOT_FOUND)
        return UACPI_ITERATION_DECISION_CONTINUE;
    if (st != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("failed to evaluate _PRT\n");
        return UACPI_ITERATION_DECISION_CONTINUE;
    }

    pci_path_t path;
    memset(&path, 0, sizeof(path));

    const char *p = uacpi_namespace_node_generate_absolute_path(node);
    DEBUG_ACPI("_PRT on '%s', path from host bridge:\n", p);

    uacpi_namespace_node *host_bridge = ctx;
    uacpi_namespace_node *curr = node;

    if (curr == host_bridge) {
        DEBUG_ACPI("(is host bridge)\n");
    } else {
        while (curr && curr != host_bridge) {
            uacpi_u64 adr;
            if (uacpi_eval_adr(curr, &adr) != UACPI_STATUS_OK) {
                DEBUG_ACPI_ERR("failed to evaluate ADR, skip\n");
                goto prt_bail;
            }

            uint8_t dev = adr >> 16;
            uint8_t fn = adr & 0xffff;

            if (dev >= 32 || fn >= 8) {
                DEBUG_ACPI_ERR("malformed _ADR 0x%lx\n", adr);
                goto prt_bail;
            }

            if (path.depth == ACPI_MAX_PCI_PATH_DEPTH) {
                DEBUG_ACPI_ERR("depth greater than ACPI_MAX_PCI_PATH_DEPTH, consider increasing\n");
                goto prt_bail;
            }

            DEBUG_ACPI("  hop: _ADR 0x%lx (dev 0x%02hhx fn %hhu)\n", adr, dev, fn);
            path.devfn[path.depth] = (dev << 3) | fn;
            path.depth++;

            curr = uacpi_namespace_node_parent(node);
        }

        /* We promised in information.h that the path is top (host bridge) down, but we
         * walked bottom up so we need to reverse the entries. */
        for (uint8_t i = 0; i < path.depth / 2; i++) {
            uint8_t tmp = path.devfn[i];
            path.devfn[i] = path.devfn[path.depth - 1 - i];
            path.devfn[path.depth - 1 - i] = tmp;
        }
    }

    for (uacpi_size i = 0; i < prt->num_entries; i++) {
        uacpi_pci_routing_table_entry *e = &prt->entries[i];
        uint32_t address = e->address >> 16;
        uint8_t pin = e->pin;

        if (e->source) {
            // @billn revisit
            DEBUG_ACPI_ERR("ohno, interrupt link device, implement me!\n");
            continue;
        }

        uint32_t gsi = e->index;

        DEBUG_ACPI("  slot 0x%x, pin %u, gsi %u\n", address, pin, gsi);

        // todo later make prt entry
    }

prt_bail:
    uacpi_free_absolute_path(p);
    uacpi_free_pci_routing_table(prt);
    return UACPI_ITERATION_DECISION_CONTINUE;
}

static uacpi_iteration_decision pci_host_bridge_cb(void *cookie, uacpi_namespace_node *node, uacpi_u32 depth)
{
    if (handover->num_host_bridges == ACPI_MAX_NUM_HOST_BRIDGES) {
        DEBUG_ACPI_ERR("Max num host bridge reached, consider increasing ACPI_MAX_NUM_HOST_BRIDGES\n");
        return UACPI_ITERATION_DECISION_BREAK;
    }

    /* Get segment and bus, allowing us to match this with an ECAM entry */
    uint64_t segment = 0;
    uacpi_status segment_eval_result = uacpi_eval_simple_integer(node, "_SEG", &segment);
    if (segment_eval_result == UACPI_STATUS_NOT_FOUND) {
        segment = 0;
    } else if (segment_eval_result != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("failed to evaluate bridge segment\n");
        return UACPI_ITERATION_DECISION_BREAK;
    }

    uint64_t start_bus = 0;
    uacpi_status start_bus_eval_result = uacpi_eval_simple_integer(node, "_BBN", &start_bus);
    if (start_bus_eval_result == UACPI_STATUS_NOT_FOUND) {
        start_bus = 0;
    } else if (start_bus_eval_result != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("failed to evaluate bridge start bus\n");
        return UACPI_ITERATION_DECISION_BREAK;
    }

    /* Get the MMIO aperatures of this host bridge, aka "Current Resource Settings". */
    DEBUG_ACPI("pulling CRS for host bridge segment %lu, start bus %lu\n", segment, start_bus);
    if (uacpi_for_each_device_resource(node, "_CRS", crs_cb, cookie) != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("failed to evaluate _CRS\n");
    }

    /* Get the "PCI Routing Table" (PRT) of the host bridge itself, and its children ports so we know
     * how the interrupts are physically wired, i.e. how (slot, pin) maps to GSI on the bus below this node. */
    prt_cb(node, node, 0);
    uacpi_namespace_for_each_child(node, prt_cb, NULL, UACPI_OBJECT_DEVICE_BIT, UACPI_MAX_DEPTH_ANY, node);

    handover->host_bridges[handover->num_host_bridges].segment = segment;
    handover->host_bridges[handover->num_host_bridges].start_bus = start_bus;
    handover->num_host_bridges++;
    return UACPI_ITERATION_DECISION_CONTINUE;
}

bool sddf_uacpi_retrieve_information(acpi_handover_t *acpi_handover)
{
    handover = acpi_handover;
    memset(handover, 0, sizeof(acpi_handover_t));

    /* For each PCIe host bridge, call pci_host_bridge_cb() */
    if (uacpi_find_devices("PNP0A03", pci_host_bridge_cb, NULL) != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("failed to enumerate PCI bridges\n");
        return false;
    }

    handover->magic = ACPI_HANDOVER_MAGIC;
    return true;
}