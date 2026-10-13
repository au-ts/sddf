/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/util/util.h>

#define CONFIG_DEBUG_DRIVER

#if defined(CONFIG_DEBUG_DRIVER)
#define DEBUG_DRIVER(fmt, ...) \
    sddf_dprintf("PCI DRIVER %s:%d|INFO: " fmt, __func__, __LINE__, ##__VA_ARGS__)
#else
#define DEBUG_DRIVER(fmt, ...) do {} while (0)
#endif

#define DEBUG_DRIVER_ERR(fmt, ...) \
    sddf_dprintf("PCI DRIVER %s:%d|ERROR: " fmt, __func__, __LINE__, ##__VA_ARGS__)

const char *pci_class_and_subclass_to_string(uint8_t class, uint8_t subclass);

void dump_acpi_info(acpi_handover_t *post_acpi_handover);
