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

#define IMX_GPIO_PIN_COUNT      160 // 5 * 32 (some actually dont exist though)
#define IMX_GPIO_INSTANCE_COUNT   5

typedef enum {
    IMX_GPIO_INSTANCE_GPIO_1  = 0,
    IMX_GPIO_INSTANCE_GPIO_2  = 32,
    IMX_GPIO_INSTANCE_GPIO_3  = 64,
    IMX_GPIO_INSTANCE_GPIO_4  = 96,
    IMX_GPIO_INSTANCE_GPIO_5  = 128,
    IMX_GPIO_ERROR_INVALID_PIN = IMX_GPIO_PIN_COUNT
} imx_gpio_instance_t;

// we use channels 30 - 61 in the driver for device <=> driver irqs
#define IMX_GPIO_IRQ_CHANNEL_START 44
#define IMX_GPIO_IRQ_CHANNEL_COUNT 18

// these are the PREDFINED values used for device <=> driver communiation
typedef enum {
    IMX_GPIO_IRQ_AH_GPIO1_7 = IMX_GPIO_IRQ_CHANNEL_START,
    IMX_GPIO_IRQ_AH_GPIO1_6,
    IMX_GPIO_IRQ_AH_GPIO1_5,
    IMX_GPIO_IRQ_AH_GPIO1_4,
    IMX_GPIO_IRQ_AH_GPIO1_3,
    IMX_GPIO_IRQ_AH_GPIO1_2,
    IMX_GPIO_IRQ_AH_GPIO1_1,
    IMX_GPIO_IRQ_AH_GPIO1_0,
    // the following are combined signals!
    IMX_GPIO_IRQ_GPIO1_0_15,
    IMX_GPIO_IRQ_GPIO1_16_31,
    IMX_GPIO_IRQ_GPIO2_0_15,
    IMX_GPIO_IRQ_GPIO2_16_31,
    IMX_GPIO_IRQ_GPIO3_0_15,
    IMX_GPIO_IRQ_GPIO3_16_31,
    IMX_GPIO_IRQ_GPIO4_0_15,
    IMX_GPIO_IRQ_GPIO4_16_31,
    IMX_GPIO_IRQ_GPIO5_0_15,
    IMX_GPIO_IRQ_GPIO5_16_31,
} imx_gpio_irq_t;

/*
================================================================================
=================================  FUNCTIONS  ==================================
================================================================================
*/

// there are drive strengths and other things we can configure , like the SION stuff

typedef enum {
    IMX_GPIO_IRQ_EDGE = GPIO_IRQ_CONFIG_PLATFORM_SPECIFIC_START,
    IMX_GPIO_IRQ_STATUS
} imx_gpio_irq_config_t;

typedef enum {
    IMX_GPIO_IRQ_LOW_LEVEL,
    IMX_GPIO_IRQ_HIGH_LEVEL,
    IMX_GPIO_IRQ_RISING_EDGE,
    IMX_GPIO_IRQ_FALLING_EDGE,
    IMX_GPIO_IRQ_ANY_EDGE,
} imx_gpio_irq_config_edge_t;

typedef enum {
    IMX_GPIO_IRQ_CONDITION_MET,
    IMX_GPIO_IRQ_CONDITION_NOT_MET,
} imx_gpio_irq_config_status_t;

