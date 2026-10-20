/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/vspace.h>

#include "internal.h"

static bool map_bars_to_client(pcie_drv_state_t *driver_state, size_t client_id, size_t spec_id,
                               pcie_func_table_idx_t function_id)
{
    pcie_connection_resource_t *client_cfg = &driver_state->config->clients[client_id];
    pcie_device_spec_t *client_spec = &client_cfg->specs[spec_id];
    pcie_function_t *function = &driver_state->funcs_table[driver_state->spec_to_func[client_id][spec_id]];

    for (size_t b = 0; b < PCI_TYPE_0_NUM_BARS; b++) {
        if (client_spec->bars[b].entry_valid) {
            assert(function->bars[b].valid);
            assert(client_spec->bars[b].entry_valid);

            uint64_t paddr = function->bars[b].paddr;
            uint64_t size = function->bars[b].size_bytes;
            uint64_t map_addr = client_spec->bars[b].map_addr;

            DEBUG_DRIVER("\t\tMapping BAR %zu, paddr 0x%lx, size 0x%lx bytes, map addr 0x%lx\n", b, paddr, size,
                         map_addr);

            seL4_CPtr client_vspace_cptr = microkit_cspace_root_slot_to_cptr(client_cfg->vspace_slot);
            if (!map_memory_region(&driver_state->handover->shadow_cnode, client_vspace_cptr, paddr, size, false,
                                   map_addr, seL4_ReadWrite, seL4_X86_Uncacheable)) {
                DEBUG_DRIVER_ERR("Failed to map BAR %zu, paddr 0x%lx, size 0x%lx bytes, map addr 0x%lx\n", b, paddr,
                                 size, map_addr);
                return false;
            }
        }
    }

    return true;
}

static bool map_intx_to_client(pcie_drv_state_t *driver_state, size_t client_id, size_t spec_id,
                               pcie_func_table_idx_t function_id)
{
    pcie_connection_resource_t *client_cfg = &driver_state->config->clients[client_id];
    pcie_device_spec_t *client_spec = &client_cfg->specs[spec_id];
    pcie_function_t *function = &driver_state->funcs_table[driver_state->spec_to_func[client_id][spec_id]];

    if (client_spec->map_intx) {
        DEBUG_DRIVER("\t\tMapping INTx GSI %u to client channel ID %u\n", function->gsi, client_spec->ch_id);
    } else {
        DEBUG_DRIVER("\t\tINTx mapping not requested by spec.\n");
    }

    return true;
}

bool bind_functions_to_clients(pcie_drv_state_t *driver_state)
{
    DEBUG_DRIVER("Binding PCIe functions to clients\n");

    for (size_t c = 0; c < driver_state->config->num_clients; c++) {
        pcie_connection_resource_t *client_cfg = &driver_state->config->clients[c];
        for (size_t s = 0; s < client_cfg->num_specs; s++) {
            pcie_func_table_idx_t function_id = driver_state->spec_to_func[c][s];
            assert(function_id != FUNCTION_TABLE_INDEX_NONE);

            pcie_function_t *function = &driver_state->funcs_table[function_id];

            /* By this point, `match_specs_to_functions()` would have checked that all
             * the specs are sane and matched each spec to exactly 1 PCIe function, so
             * we don't bother with checking the spec again. */

            DEBUG_DRIVER("\tBinding %02x:%02x.%x to client %lu spec %lu\n", function->bus, function->dev,
                         function->func, c, s);

            if (!map_bars_to_client(driver_state, c, s, function_id)) {
                return false;
            }
            if (!map_intx_to_client(driver_state, c, s, function_id)) {
                return false;
            }
        }
    }

    return true;
}