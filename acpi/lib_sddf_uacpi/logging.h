/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/util/printf.h>

#define CONFIG_DEBUG_ACPI

#if defined(CONFIG_DEBUG_ACPI)
#define DEBUG_ACPI(fmt, ...) \
    sddf_dprintf("ACPI %s:%d|INFO: " fmt, __func__, __LINE__, ##__VA_ARGS__)
#else
#define DEBUG_ACPI(fmt, ...) do {} while (0)
#endif

#define DEBUG_ACPI_ERR(fmt, ...) \
    sddf_dprintf("ACPI %s:%d|ERROR: " fmt, __func__, __LINE__, ##__VA_ARGS__)
