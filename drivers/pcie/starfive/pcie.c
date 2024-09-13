/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

uint32_t *pcie_regs;
uint32_t *pcie_config;

void init()
{
    sddf_dprintf("pcie driver starting!\n");

    sddf_dprintf("PRINTING PCIE REGS\n");
    for (int i = 0; i < 1024; i++) {
        sddf_dprintf("[%04d]: 0x%x\n", i, pcie_regs[i]);
    }
    sddf_dprintf("PRINTING PCIE CONFIG\n");
    for (int i = 0; i < 1024; i++) {
        sddf_dprintf("[%04d]: 0x%x\n", i, pcie_config[i]);
    }
}

void notified(microkit_channel ch)
{
}

