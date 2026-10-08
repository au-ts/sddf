/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/util/printf.h>

#define COLOUR_RED     "\x1b[31m"
#define COLOUR_GREEN   "\x1b[32m"
#define COLOUR_YELLOW  "\x1b[33m"
#define COLOUR_BLUE    "\x1b[34m"
#define COLOUR_RESET   "\x1b[0m"

#define CONFIG_DEBUG_ACPI

#if defined(CONFIG_DEBUG_ACPI)
#define DEBUG_ACPI(fmt, ...) \
    sddf_dprintf("LIB ACPI %s:%d|INFO: " fmt, __func__, __LINE__, ##__VA_ARGS__)
#else
#define DEBUG_ACPI(fmt, ...) do {} while (0)
#endif

#define DEBUG_ACPI_WARN(fmt, ...) \
    sddf_dprintf("LIB ACPI %s:%d|WARN: " fmt, __func__, __LINE__, ##__VA_ARGS__)

#define DEBUG_ACPI_ERR(fmt, ...) \
    sddf_dprintf("LIB ACPI %s:%d|ERROR: " fmt, __func__, __LINE__, ##__VA_ARGS__)
