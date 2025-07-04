/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* Shared functionality/definitions between timer drivers and clients */

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

- all the current platforms are little endian as well
REQUESTS:

We currently are splitting the fields up like this

Bits [0 : 9]

- will contain the interface enum

typedef enum  {
    GPIO_SET_VALUE,
    GPIO_GET_VALUE,
    GPIO_SET_DIRECTION,
    GPIO_GET_DIRECTION,
    GPIO_GET_IRQ_CONFIGURATION,
    GPIO_SET_IRQ_CONFIGURATION,
    GPIO_GET_PIN_CONFIGURATION,
    GPIO_SET_PIN_CONFIGURATION,
} GPIO_interface_t;


Bits [10 : 19] 

- will contain the config value

RESPONSES:

- the twentieth bit marks if its an error or not (1 is an error)
- the other bits marks the return value 

*/

// NOTE: these will appear as negative numbers to clients
typedef enum {
	GPIO_ERROR_NOT_IMPLEMENTED = 1,
    GPIO_ERROR_INVALID_NUM_ARGS = 2,       // Incorrect number of arguments
    GPIO_ERROR_INVALID_LABEL = 3,          // Incorrect label
    GPIO_ERROR_INVALID_CONFIG = 4,         // Invalid configuration
    GPIO_ERROR_INVALID_VALUE = 5,          // Invalid value
    GPIO_ERROR_UNSUPPORTED_PIN_CONFIG = 6, // Requested config not supported for this pin
    GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG = 7, // Requested config not supported for this IRQ
    GPIO_ERROR_PERMISSION_DENIED = 8       // Operation not allowed due to whats stated in the gpio_driver_channel_mappings 
} gpio_error_t;

typedef enum {
	GPIO_DIRECTION_INPUT = 0,
	GPIO_DIRECTION_OUTPUT = 1,
} GPIO_direction_t;

// NOTE: some of these might not be implemented in the driver
// TODO: fix
typedef enum {
    GPIO_IRQ_TYPE_NONE = 0,
    GPIO_IRQ_TYPE_EDGE_RISING,
    GPIO_IRQ_TYPE_EDGE_FALLING,
    GPIO_IRQ_TYPE_EDGE_BOTH,
    GPIO_IRQ_TYPE_LEVEL_HIGH,
    GPIO_IRQ_TYPE_LEVEL_LOW,
    GPIO_IRQ_TYPE_LEVEL_BOTH // may not be neccesary as linux doesn't do it but should check the meson driver as well
} GPIO_irq_configuration_t;

// #define IRQ_TYPE_NONE		0
// #define IRQ_TYPE_EDGE_RISING	1
// #define IRQ_TYPE_EDGE_FALLING	2
// #define IRQ_TYPE_EDGE_BOTH	(IRQ_TYPE_EDGE_FALLING | IRQ_TYPE_EDGE_RISING)
// #define IRQ_TYPE_LEVEL_HIGH	4
// #define IRQ_TYPE_LEVEL_LOW	8

// NOTE: these are not implemented, but are here for reference as to how it could be used
typedef enum {
	GPIO_PULL_UP,
	GPIO_PULL_DOWN,
	GPIO_NO_PULL,
	GPIO_DRIVE_STRENGTH,
} GPIO_pin_configuration_t;


// linux/include/dt-bindings/interrupt-controller/irq.h
// linux/include/dt-bindings/gpio/gpio.h

// Probably need to put the linear scheme here as well?













