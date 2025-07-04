/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include <sddf/gpio/protocol.h>
#include "gpio.h"
#include <gpio_config.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

void notified(microkit_channel ch)
{
    // right now the IRQs are not mapped but we already know that it
    // works anyway
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    sddf_dprintf("GPIO DRIVER|LOG: ppc notification from channel %u\n", ch);

    // check the config file to see the permissions
    // can they edit this



    return microkit_msginfo_new(0, 0);
}

void init(void)
{
	assert(device_resources_check_magic(&device_resources));

	// we mapped 8 irqs but they arent in the config file so they wont get included?
    // assert(device_resources.num_irqs == 0);

    sddf_dprintf("GPIO DRIVER|LOG: Is gpio_driver_channel_mappings included : %d\n", gpio_driver_channel_mappings[0].pin);


    // right now its just the one node for the interrupt controller registers
    // assert(device_resources.num_regions == 1);

    // regs = (void *)((uintptr_t)device_resources.regions[0].region.vaddr + TIMER_REG_START);
}

// 2. we just turn one of the LEDs on
// 	3. then we go into the notified for some input
// 	4. we could even do this with another led so we dont need an external button