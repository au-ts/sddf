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

// Hardware memory
uintptr_t gpio_regs = 0x30000000;
uintptr_t irq_con_regs = 0x30100000;

// For O(1) lookups
static int pin_subscriber[8] = {-1};

void notified(microkit_channel ch)
{
    switch (ch) {
    case 54:
    case 55:
    case 56:
    case 57:
    case 58:
    case 59:
    case 60:
    case 61:
        microkit_notify(pin_subscriber[ch - 54]);
        break;
    default:
        break;
    }
}


seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    sddf_dprintf("GPIO DRIVER|LOG: ppc notification from channel %u\n", ch);
}

void init(void)
{
	assert(device_resources_check_magic(&device_resources));

    assert(device_resources.num_irqs == 0);
    assert(device_resources.num_regions == 0);
}
