/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * GPIOX6 is used for PWM_A
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>

void init(void)
{
    sddf_dprintf("--------------------\n");
    sddf_dprintf("Clock frequency measurement\n");


    sddf_dprintf("--------------------\n");

}

void notified(microkit_channel ch)
{

}
