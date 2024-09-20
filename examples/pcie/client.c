/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>

void notified(microkit_channel ch)
{

}

void init(void)
{
    sddf_dprintf("Hello from client\n");
}
