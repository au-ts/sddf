/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */


#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>

uintptr_t clk_regs;

void notified(microkit_channel ch)
{

}

void init(void)
{
    sddf_dprintf("Clock driver initialising...\n");
}
