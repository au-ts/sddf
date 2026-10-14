/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

#define PCI_DEVICE_SPEC_VENDOR_ID_ANY 0xFFFF
#define PCI_DEVICE_SPEC_DEVICE_ID_ANY 0xFFFF
#define PCI_DEVICE_SPEC_CLASS_CODE_ANY 0xFFFFFFFF

typedef struct {
    uint16_t instance;
    uint16_t vendor, device;
    uint32_t class_code;    /* class:subclass:prog-if */
} pci_device_spec_t;
