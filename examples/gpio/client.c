/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/gpio/client.h>
#include <sddf/gpio/config.h>
#include <sddf/util/printf.h>
#include <os/sddf.h>

__attribute__((__section__(".gpio_client_config"))) gpio_client_config_t config;

// @ Tristan : will need to change this
microkit_channel gpio_channel_1_output;
microkit_channel gpio_channel_2_output;
microkit_channel gpio_channel_3_input;


// @ TRistan : add coroutines later
void notified(microkit_channel ch)
{
   sddf_printf("CLIENT|INFO: Got an interupt from GPIO!\n"); 
}

void init(void)
{
    sddf_printf("CLIENT|INFO: starting\n");

    assert(gpio_config_check_magic(&config));

    gpio_channel_1_output = config.driver_channel_ids[0];
    gpio_channel_2_output = config.driver_channel_ids[1];

    sddf_ppcall(gpio_channel_1_output, seL4_MessageInfo_new(2, 0, 0, 1));
    sddf_ppcall(gpio_channel_2_output, seL4_MessageInfo_new(3, 0, 0, 1));
}
