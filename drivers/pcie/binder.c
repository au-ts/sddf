/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <microkit.h>

#include "internal.h"

bool bind_functions_to_clients(pcie_drv_state_t *driver_state)
{
    DEBUG_DRIVER("Binding PCIe functions to clients\n");

    // for (size_t c = 0; c < driver_state->config->num_clients; c++) {
    //     pcie_connection_resource_t *client_cfg = &driver_state->config->clients[c];
    //     for (size_t s = 0; s < client_cfg->num_specs; s++) {
    //         pcie_device_spec_t *client_spec = &client_cfg->specs[s];
    //     }
    // }

    return true;
}