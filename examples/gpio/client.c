/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/gpio/client.h>
#include <sddf/gpio/config.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".gpio_client_config"))) gpio_client_config_t config;

// @ Tristan : will need to change this
microkit_channel gpio_channel;

// @ TRistan : add coroutines later

void notified(microkit_channel ch)
{
}

void init(void)
{
    sddf_printf("CLIENT|INFO: starting\n");

    assert(gpio_config_check_magic(&config));

    // gpio_channel = config.driver_id;
}
