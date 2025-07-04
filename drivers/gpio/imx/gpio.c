/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include <sddf/gpio/protocol.h>
#include <gpio_config.h>
#include "gpio.h"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

// volatile struct gpio_regs *regs;

void notified(microkit_channel ch)
{
    
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    sddf_dprintf("GPIO DRIVER|LOG: ppc notification from channel %u\n", ch);

    return microkit_msginfo_new(0, 0);
}

void init(void)
{
	assert(device_resources_check_magic(&device_resources));

    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    sddf_dprintf("GPIO DRIVER|LOG: Is gpio_driver_channel_mappings included : %d\n", gpio_driver_channel_mappings[0].pin);
}
