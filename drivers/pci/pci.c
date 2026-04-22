/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "pci.h"

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>

uintptr_t pci_resource;

void init(void)
{
    sddf_dprintf("PCI driver\n");
}

void notified(microkit_channel ch)
{
}
