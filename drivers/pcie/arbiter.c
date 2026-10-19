/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <microkit.h>

#include "internal.h"

static bool spec_matches(pcie_device_spec_t *spec, pcie_function_t *candidate)
{
    volatile pci_conf_space_endpoint_t *candidate_cs = candidate->cs;

    if (spec->vendor != SDDF_PCIE_DEVICE_SPEC_VENDOR_ID_ANY) {
        uint16_t candidate_vendor = candidate_cs->hdr.vendor_id;
        if (candidate_vendor != spec->vendor) {
            DEBUG_DRIVER("\tnot a match to %02x:%02x.%x because actual vendor code 0x%x != wanted vendor code 0x%x\n",
                         candidate->bus, candidate->dev, candidate->func, candidate_vendor, spec->vendor);
            return false;
        }
    }

    if (spec->device != SDDF_PCIE_DEVICE_SPEC_DEVICE_ID_ANY) {
        uint16_t candidate_device = candidate_cs->hdr.device_id;
        if (candidate_device != spec->device) {
            DEBUG_DRIVER("\tnot a match to %02x:%02x.%x because actual device code 0x%x != wanted device "
                         "code 0x%x\n",
                         candidate->bus, candidate->dev, candidate->func, candidate_device, spec->device);
            return false;
        }
    }

    if (spec->function != SDDF_PCIE_DEVICE_SPEC_FUNCTION_ID_ANY) {
        if (candidate->func != spec->function) {
            DEBUG_DRIVER("\tnot a match to %02x:%02x.%x because actual function number 0x%x != wanted "
                         "function number 0x%x\n",
                         candidate->bus, candidate->dev, candidate->func, candidate->func, spec->function);
            return false;
        }
    }

    if (spec->class_code != SDDF_PCIE_DEVICE_SPEC_CLASS_CODE_ANY) {
        uint32_t candidate_class_code = candidate_cs->hdr.prog_if;
        candidate_class_code |= ((uint32_t)(candidate_cs->hdr.subclass)) << 8;
        candidate_class_code |= ((uint32_t)(candidate_cs->hdr.class_code)) << 16;
        if (candidate_class_code != spec->class_code) {
            DEBUG_DRIVER("\tnot a match to %02x:%02x.%x because actual class code 0x%x != wanted class code 0x%x\n",
                         candidate->bus, candidate->dev, candidate->func, candidate_class_code, spec->class_code);
            return false;
        }
    }

    return true;
}

bool match_specs_to_functions(pcie_drv_state_t *driver_state)
{
    DEBUG_DRIVER("Starting PCIe client spec to function matcher\n");
    size_t successful_matches = 0, required_matches = 0;

    for (size_t c = 0; c < driver_state->config->num_clients; c++) {
        pcie_connection_resource_t *client_cfg = &driver_state->config->clients[c];
        for (size_t s = 0; s < client_cfg->num_specs; s++) {
            pcie_device_spec_t *client_spec = &client_cfg->specs[s];
            required_matches += 1;

            pcie_func_table_idx_t bound = FUNCTION_TABLE_INDEX_NONE;
            size_t num_matches = 0;

            DEBUG_DRIVER("attempting to match client %lu's spec %lu to a PCIe function\n", c, s);
            for (size_t f = 0; f < driver_state->num_funcs; f++) {
                pcie_function_t *candidate_func = &driver_state->funcs_table[f];

                if (!spec_matches(client_spec, candidate_func)) {
                    continue;
                }
                if (bound == FUNCTION_TABLE_INDEX_NONE) {
                    if (client_spec->instance == SDDF_PCIE_DEVICE_INSTANCE_ANY
                        || num_matches == client_spec->instance) {
                        bound = f;
                    }
                }

                num_matches++;
            }

            pcie_function_t *matched_func = &driver_state->funcs_table[bound];

            if (bound == FUNCTION_TABLE_INDEX_NONE) {
                DEBUG_DRIVER_ERR("\tclient %lu spec %lu: not a match to any function\n", c, s);
                continue;
            }
            if (client_spec->instance == SDDF_PCIE_DEVICE_INSTANCE_ANY && num_matches > 1) {
                DEBUG_DRIVER_ERR("\tclient %lu spec %lu: matched %zu functions, ambiguous spec!\n", c, s, num_matches);
                continue;
            }
            if (matched_func->owner != PCIE_FUNC_OWNER_NONE) {
                DEBUG_DRIVER_ERR("\tclient %lu spec %lu: matched %02x:%02x.%x, but already bound to client %d\n", c, s,
                                 matched_func->bus, matched_func->dev, matched_func->func, matched_func->owner);
                continue;
            }

            bool bars_spec_ok = true;
            assert(SDDF_PCIE_DEVICE_MAX_NUM_BARS == PCI_TYPE_0_NUM_BARS);
            for (int b = 0; b < PCI_TYPE_0_NUM_BARS; b++) {
                if (!client_spec->bars[b].entry_valid) {
                    continue;
                }

                if (!matched_func->bars[b].valid) {
                    DEBUG_DRIVER_ERR(
                        "\tnot a match to %02x:%02x.%x, BAR %d claimed but spec but not implemented by device\n",
                        matched_func->bus, matched_func->dev, matched_func->func, b);
                    bars_spec_ok = false;
                    break;
                }

                if (matched_func->bars[b].size_bytes > client_spec->bars[b].max_size) {
                    DEBUG_DRIVER_ERR("\tnot a match to %02x:%02x.%x, BAR %d actual 0x%lx bytes greater than max 0x%lx "
                                     "bytes in spec\n",
                                     matched_func->bus, matched_func->dev, matched_func->func, b,
                                     matched_func->bars[b].size_bytes, client_spec->bars[b].max_size);
                    bars_spec_ok = false;
                    break;
                }

                if (matched_func->bars[b].size_bytes < client_spec->bars[b].min_size) {
                    DEBUG_DRIVER_ERR(
                        "\tnot a match to %02x:%02x.%x, BAR %d actual 0x%lx bytes lower than min 0x%lx bytes in spec\n",
                        matched_func->bus, matched_func->dev, matched_func->func, b, matched_func->bars[b].size_bytes,
                        client_spec->bars[b].min_size);
                    bars_spec_ok = false;
                    break;
                }
            }

            if (bars_spec_ok) {
                DEBUG_DRIVER("\tmatched to %02x:%02x.%x\n", matched_func->bus, matched_func->dev, matched_func->func);
                successful_matches += 1;

                driver_state->spec_to_func[c][s] = bound;
                matched_func->owner = c;
            }
        }
    }

    if (required_matches && successful_matches != required_matches) {
        DEBUG_DRIVER_ERR("Required != Successful: %lu != %lu\n", required_matches, successful_matches);
        return false;
    }

    DEBUG_DRIVER("Successfully matched all %lu specs\n", successful_matches);
    return true;
}