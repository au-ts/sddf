/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/util/util.h>
#include <stdint.h>


// Shared functionality/definitions between gpio drivers and clients

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

typedef enum {
    SDDF_GPIO_LINE_DIRECTION_OUT = 0,
    SDDF_GPIO_LINE_DIRECTION_IN  = 1,
} SDDF_GPIO_line_direction_t;

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

#define GPIO_VALUE_SHIFT 10
#define GPIO_VALUE_WIDTH 10

#define GPIO_ENCODE_VALUE(val) (((val) & BIT_MASK(GPIO_VALUE_WIDTH)) << GPIO_VALUE_SHIFT)
#define GPIO_DECODE_VALUE(label) (((label) >> GPIO_VALUE_SHIFT) & BIT_MASK(GPIO_VALUE_WIDTH))

/**
 * Encode a raw 10-bit value into bits [19:10] of a label.
 */
static inline uint32_t gpio_encode_value(uint32_t val) {
    // shift up, then mask to that [19:10] window
    return (val << GPIO_VALUE_SHIFT)
         & BIT_MASK_RANGE(
               GPIO_VALUE_SHIFT + GPIO_VALUE_WIDTH - 1,
               GPIO_VALUE_SHIFT
           );
}

/**
 * Decode bits [19:10] from a 32-bit label into a 10-bit value.
 */
static inline uint32_t gpio_decode_value(uint32_t label) {
    // mask to [19:10], then shift down
    return (label
           & BIT_MASK_RANGE(
               GPIO_VALUE_SHIFT + GPIO_VALUE_WIDTH - 1,
               GPIO_VALUE_SHIFT
             ))
         >> GPIO_VALUE_SHIFT;
}

#define SDDF_GPIO_RESPONSE_ERROR_BIT 19
#define SDDF_GPIO_RESPONSE_VALUE_MASK BIT_MASK_RANGE(18, 0)

// TODO: come up with interface for set_configs config

typedef enum {
    SDDF_GPIO_EOPNOTSUPP = 1,
    SDDF_GPIO_EINVAL = 2,
    SDDF_GPIO_EPERM = 3
} gpio_error_t;
