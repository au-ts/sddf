/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
// #include "pci.h"

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/vspace.h>

#include "internal.h"

acpi_handover_t *post_acpi_handover;
static pcie_drv_state_t drv_state;

__attribute__((__section__(".pcie_driver_config"))) pcie_driver_config_t config;

void init(void)
{
    /* @billn for testing only, remove after metaprogram integration */
    config.num_clients = 1;
    config.clients[0] = (pcie_connection_resource_t) {
        .id = 1,
        .cspace_slot = 3,
        .vspace_slot = 4,
        .vspace_is_x86_ept = 0,
        .num_specs = 1,
        .specs[0] = (pcie_device_spec_t) {
            .bus_master = 1,
            .class_code = 0x00010802, /* 0x1 Mass Storage Controller, 0x8 Non Volatile Mem Controller, 0x2 NVMe */
            .device = SDDF_PCIE_DEVICE_SPEC_DEVICE_ID_ANY,
            .vendor = SDDF_PCIE_DEVICE_SPEC_VENDOR_ID_ANY,
            .function = SDDF_PCIE_DEVICE_SPEC_FUNCTION_ID_ANY,
            .instance = SDDF_PCIE_DEVICE_INSTANCE_ANY,
        },
    };

    memset(&drv_state, 0, sizeof(drv_state));
    for (size_t c = 0; c < SDDF_PCIE_MAX_CLIENTS; c++) {
        for (size_t s = 0; s < SDDF_PCIE_MAX_DEVICE_SPECS_PER_CLIENT; s++) {
            drv_state.spec_to_func[c][s] = FUNCTION_TABLE_INDEX_NONE;
        }
    }
    drv_state.vaddr_watermark = BIT(32);
    drv_state.handover = post_acpi_handover;
    drv_state.config = &config;

    DEBUG_DRIVER("Blocking on ACPI driver handover\n");
    microkit_msginfo msginfo = microkit_msginfo_new(0, 0);
    microkit_ppcall(ACPI_DRIVER_CH, msginfo);
    DEBUG_DRIVER("ACPI driver handover complete\n");

    if (post_acpi_handover->magic != ACPI_HANDOVER_MAGIC) {
        DEBUG_DRIVER_ERR("ACPI handover have bad magic: %x != %x\n", post_acpi_handover->magic, ACPI_HANDOVER_MAGIC);
        return;
    }

#ifdef CONFIG_DEBUG_DRIVER
    dump_acpi_info(post_acpi_handover);
#endif

    if (!map_ecams(&drv_state))
        return;
    if (!host_bridges_scan(&drv_state))
        return;
    if (!match_specs(&drv_state))
        return;

    drv_state.initialised = true;
}

void notified(microkit_channel ch)
{
    DEBUG_DRIVER_ERR("Unexpected notification on channel %u\n", ch);
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    if (!drv_state.initialised) {
        /* Impossible, init always return before protected can be called by the Microkit event loop. */
        assert(false);
    }

    return microkit_msginfo_new(0, 0);
}