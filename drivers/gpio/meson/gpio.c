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

static inline seL4_MessageInfo_t error_response(gpio_error_t error_code) {
    uint32_t e = error_code | BIT(SDDF_GPIO_RESPONSE_ERROR_BIT);
    return microkit_msginfo_new(e, 0);
}

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

    // Parse the label
    uint32_t label = microkit_msginfo_get_label(msginfo);
    uint32_t interface_function = label & SDDF_REQUEST_INTERFACE_MASK;
    uint32_t value = label & GPIO_REQUEST_VALUE_MASK;

    // Check what pin it has
    int pin = gpio_driver_channel_mappings[ch].pin;
    int irq = gpio_driver_channel_mappings[ch].irq;

    switch (interface_function) {
    case SDDF_GPIO_SET: {
        // return set(pin, value);
        return error_response(SDDF_GPIO_EOPNOTSUPP);
    }
    case SDDF_GPIO_GET: {
        // return get(pin);
        return error_response(SDDF_GPIO_EOPNOTSUPP);
    }
    case SDDF_GPIO_DIRECTION_OUTPUT: {
        // return set_direction_output(pin, value);
        return error_response(SDDF_GPIO_EOPNOTSUPP);
    }
    case SDDF_GPIO_DIRECTION_INPUT: {
        // return set_direction_input(pin);
        return error_response(SDDF_GPIO_EOPNOTSUPP);
    }
    case SDDF_GPIO_GET_DIRECTION: {
        // return get_direction(pin);
        return error_response(SDDF_GPIO_EOPNOTSUPP);
    }
    case SDDF_GPIO_SET_CONFIG: {
        uint32_t arguement = seL4_GetMR(0);
        // return set_config(pin, value, arguement);
        return error_response(SDDF_GPIO_EOPNOTSUPP);
    }
    // case SDDF_GPIO_IRQ_ENABLE: {
    //     if (check_irq_permissions)
    //     return irq_enable(pin);
    // }
    // case SDDF_GPIO_IRQ_DISABLE: {
    //     return irq_disable(pin);
    // }
    // case SDDF_GPIO_IRQ_SET_TYPE: {
    //     return irq_set_type(pin, value);
    // }
    default:
        sddf_dprintf("GPIO DRIVER|LOG: Unknown request %lu to gpio from channel %u\n", microkit_msginfo_get_label(msginfo),
                     ch);
        return error_response(SDDF_GPIO_EOPNOTSUPP);
    } 

}

void init(void)
{
	assert(device_resources_check_magic(&device_resources));

    assert(device_resources.num_irqs == 0);
    assert(device_resources.num_regions == 0);

    sddf_dprintf("GPIO DRIVER|LOG: Is gpio_driver_channel_mappings included : %d\n", gpio_driver_channel_mappings[0].pin);
}
