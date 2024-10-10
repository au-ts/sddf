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
#include <sddf/clk/client.h>

#define CLK_DRIVER_CH 0

void init(void)
{
    sddf_dprintf("--------------------\n");
    sddf_dprintf("Clock request test\n");

    uint32_t ret = sddf_clk_enable(CLK_DRIVER_CH, 10);
    sddf_dprintf("ret_val: %x\n", ret);

    ret = sddf_clk_disable(CLK_DRIVER_CH, 24);
    sddf_dprintf("ret_val: %x\n", ret);

    ret = sddf_clk_get_rate(CLK_DRIVER_CH, 10);
    sddf_dprintf("ret_val: %x\n", ret);

    ret = sddf_clk_set_rate(CLK_DRIVER_CH, 10, 150000000);
    sddf_dprintf("ret_val: %x\n", ret);

    sddf_dprintf("--------------------\n");

}

void notified(microkit_channel ch)
{

}
