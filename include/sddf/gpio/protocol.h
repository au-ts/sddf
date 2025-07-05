/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/util/util.h>

/* Shared functionality/definitions between timer drivers and clients */

/* 

GPIO DRIVER PROTOCOL

This is modelled as similiar as possible to:
- include/linux/gpio/driver.h

Part of the gpio_chip also is an irq_chip so that functionality is modelled as
simliar as possible to:
- include/linux/irq.h

Part of the GPIO set_config is there needs to be an interface to interact with the pin configs.
So this part is modelled as similiar as possible to:
- include/linux/pinctrl/pinconf-generic.h
- Linux also offers platforms to extend this, e.g.
    - PIN_CONFIG_END = 0x7FFF,     // last generic value
    - enum imx6q_pinconf_param { IMX6Q_PINCONF_SION = PIN_CONFIG_END + 1, ... }

Everything currently provided is the lowest level of abstraction for gpio functionality.
Everything else (sysfs, dts, etc...) interfaces through these core things.
*/

/* 

DESIGN :

For the GPIO driver we never need to transfer that much infomation.
Thus for now our protocol tries to condense all the infomation into 20 bits.
The choice for 20 bits comes from the fact that the amount of words in the sel4 IPC fastpath
is 1 word in the worst case architecure (x86).
This first word is always reserved for the message tag thus we try to fit protocol data in that.
Now the tag contains label, caps unwrapped, #caps, msg length where the label is for us to define
semantics for. The other fields not including label add up to 12 bits.

- field capsUnwrapped 3
- field extraCaps 2
- field length 7

So to account for the worst case which is a 32 bit system means we only get 20 bits in the label to do what we need.
NOTE: all the current platforms are little endian as well

REQUESTS:

We currently are splitting the fields up like this

Bits [0 : 9]

- will contain the interface enum SDDF_GPIO_interface_t;

Bits [10 : 19] 

- will contain the config, value or type

MR(0)

- In some cases can be used for a config argument as well

RESPONSES:
- can currently all fit into the label
- the twentieth bit marks if its an error or not (1 is an error)
- the other bits marks the return value 

*/

// As simliar as possible to Linux
typedef enum  {
    // GPIO based
    SDDF_GPIO_SET,
    SDDF_GPIO_GET,
    SDDF_GPIO_DIRECTION_OUTPUT,
    SDDF_GPIO_DIRECTION_INPUT,
    SDDF_GPIO_GET_DIRECTION,
    SDDF_GPIO_SET_CONFIG,

    // IRQ based
    SDDF_GPIO_IRQ_ENABLE,
    SDDF_GPIO_IRQ_DISABLE,
    SDDF_GPIO_IRQ_SET_TYPE
} SDDF_GPIO_interface_t;

// Same as Linux
typedef enum {
    SDDF_GPIO_LINE_DIRECTION_OUT = 0,
    SDDF_GPIO_LINE_DIRECTION_IN  = 1,
} SDDF_GPIO_line_direction_t;

// Same as Linux
typedef enum {
    SDDF_IRQ_TYPE_NONE          = 0x00,
    SDDF_IRQ_TYPE_EDGE_RISING   = 0x01,
    SDDF_IRQ_TYPE_EDGE_FALLING  = 0x02,
    SDDF_IRQ_TYPE_EDGE_BOTH     = (SDDF_IRQ_TYPE_EDGE_FALLING | SDDF_IRQ_TYPE_EDGE_RISING),
    SDDF_IRQ_TYPE_LEVEL_HIGH    = 0x04,
    SDDF_IRQ_TYPE_LEVEL_LOW     = 0x08,
    SDDF_IRQ_TYPE_LEVEL_MASK    = (SDDF_IRQ_TYPE_LEVEL_LOW | SDDF_IRQ_TYPE_LEVEL_HIGH),
} SDDF_GPIO_irq_line_status_t;

#define SDDF_REQUEST_INTERFACE_MASK \
    BIT_MASK_RANGE(9, 0)

#define GPIO_REQUEST_VALUE_MASK \
    BIT_MASK_RANGE(19, 10)

#define SDDF_GPIO_RESPONSE_ERROR_BIT 19
#define SDDF_GPIO_RESPONSE_VALUE_MASK BIT_MASK_RANGE(18, 0)

// TODO: come up with interface for set_configs config







// NOTE: these will appear as negative numbers to clients (linux does this)
// TODO:
// typedef enum {
// 	GPIO_ERROR_NOT_IMPLEMENTED = 1,
//     GPIO_ERROR_INVALID_NUM_ARGS = 2,       // Incorrect number of arguments
//     GPIO_ERROR_INVALID_LABEL = 3,          // Incorrect label
//     GPIO_ERROR_INVALID_CONFIG = 4,         // Invalid configuration
//     GPIO_ERROR_INVALID_VALUE = 5,          // Invalid value
//     GPIO_ERROR_UNSUPPORTED_PIN_CONFIG = 6, // Requested config not supported for this pin
//     GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG = 7, // Requested config not supported for this IRQ
//     GPIO_ERROR_PERMISSION_DENIED = 8       // Operation not allowed due to whats stated in the gpio_driver_channel_mappings 
// } gpio_error_t;
