/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/gpio/gpio.h>

/* IMX SPECIFIC FORMAT FOR GPIO PPC REQUESTS/RESPONSES */

/*
================================================================================
===================================  CONVERSIONS  ==============================
================================================================================
*/

#define IMX_GPIO_PIN_COUNT      139
#define IMX_GPIO_INSTANCE_COUNT   5

typedef enum {
    IMX_GPIO_INSTANCE_GPIO_1  = 0,
    IMX_GPIO_INSTANCE_GPIO_2  = 30,
    IMX_GPIO_INSTANCE_GPIO_3  = 51,
    IMX_GPIO_INSTANCE_GPIO_4  = 77,
    IMX_GPIO_INSTANCE_GPIO_5  = 109,
    IMX_GPIO_ERROR_INVALID_PIN = IMX_GPIO_PIN_COUNT
} imx_gpio_instance_t;

// we use channels 30 - 61 in the driver for device <=> driver irqs
#define IMX_GPIO_IRQ_CHANNEL_START 30
#define IMX_GPIO_IRQ_CHANNEL_COUNT 32

// these are the PREDFINED values used for device <=> driver communiation
typedef enum {
    IMX_GPIO_IRQ_0 = IMX_GPIO_IRQ_CHANNEL_START,
    IMX_GPIO_IRQ_1,
    IMX_GPIO_IRQ_2,
    IMX_GPIO_IRQ_3,
    IMX_GPIO_IRQ_4,
    IMX_GPIO_IRQ_5,
    IMX_GPIO_IRQ_6,
    IMX_GPIO_IRQ_7,
    IMX_GPIO_IRQ_8,
    IMX_GPIO_IRQ_9,
    IMX_GPIO_IRQ_10,
    IMX_GPIO_IRQ_11,
    IMX_GPIO_IRQ_12,
    IMX_GPIO_IRQ_13,
    IMX_GPIO_IRQ_14,
    IMX_GPIO_IRQ_15,
    IMX_GPIO_IRQ_16,
    IMX_GPIO_IRQ_17,
    IMX_GPIO_IRQ_18,
    IMX_GPIO_IRQ_19,
    IMX_GPIO_IRQ_20,
    IMX_GPIO_IRQ_21,
    IMX_GPIO_IRQ_22,
    IMX_GPIO_IRQ_23,
    IMX_GPIO_IRQ_24,
    IMX_GPIO_IRQ_25,
    IMX_GPIO_IRQ_26,
    IMX_GPIO_IRQ_27,
    IMX_GPIO_IRQ_28,
    IMX_GPIO_IRQ_29,
    IMX_GPIO_IRQ_30,
    IMX_OPIO_IRQ_31,
} imx_gpio_irq_t;

/*
================================================================================
=================================  FUNCTIONS  ==================================
================================================================================
*/

typedef enum {
    IMX_GPIO_IRQ_EDGE = GPIO_IRQ_CONFIG_PLATFORM_SPECIFIC_START,
} imx_gpio_irq_config_t;

typedef enum {
    IMX_GPIO_IRQ_LOW_LEVEL,
    IMX_GPIO_IRQ_HIGH_LEVEL,
    IMX_GPIO_IRQ_RISING_EDGE,
    IMX_GPIO_IRQ_FALLING_EDGE,
    IMX_GPIO_IRQ_ANY_EDGE,
} imx_gpio_irq_config_edge_t;

