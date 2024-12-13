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

/* MESON SPECIFIC FORMAT FOR GPIO PPC REQUESTS/RESPONSES */

/*
================================================================================
===================================  CONVERSIONS  ==============================
================================================================================
*/

// PIN NUMBER = BANK NAME + BANK PIN NUMBER

#define MESON_GPIO_PIN_COUNT 101
#define MESON_GPIO_BANK_COUNT 9

typedef enum {
    GPIO_AO  = 0,
    GPIO_Z  = 12,
    GPIO_H  = 28,
    BOOT    = 37,
    GPIO_C  = 53,
    GPIO_A  = 61,
    GPIO_X  = 77,
    GPIO_E  = 97,
    TEST_N  = 100,
    GPIO_ERROR_INVALID_PIN = MESON_GPIO_PIN_COUNT
} meson_gpio_bank_t;

// we use channels 52 - 61 in the driver for device <=> driver irqs
#define MESON_GPIO_IRQ_CHANNEL_START 52
#define MESON_GPIO_IRQ_CHANNEL_COUNT 10

// these are the values used for device <=> driver communiation
typedef enum {
    GPIO_IRQ_0 = MESON_GPIO_IRQ_CHANNEL_START,
    GPIO_IRQ_1,
    GPIO_IRQ_2,
    GPIO_IRQ_3,
    GPIO_IRQ_4,
    GPIO_IRQ_5,
    GPIO_IRQ_6,
    GPIO_IRQ_7,
    GPIO_AO_IRQ_0,
    GPIO_AO_IRQ_1,
} meson_irq_gpio_t;

/*
================================================================================
=================================  FUNCTIONS  ==================================
================================================================================
*/

typedef enum {
    GPIO_PULL = GPIO_CONFIG_PLATFORM_SPECIFIC_START,
    GPIO_DRIVE_STRENGTH,
} meson_gpio_config_t;

typedef enum {
    GPIO_IRQ_EDGE = GPIO_IRQ_CONFIG_PLATFORM_SPECIFIC_START,
    GPIO_IRQ_FILTER,
} meson_gpio_irq_config_t;

typedef enum {
	GPIO_DS_500UA    = 0,
	GPIO_DS_2500UA   = 1,
	GPIO_DS_3000UA   = 2,
	GPIO_DS_4000UA   = 3,
} meson_gpio_config_drv_str_t;

typedef enum {
    GPIO_PULL_UP,
    GPIO_PULL_DOWN,
    GPIO_NO_PULL,
} meson_gpio_config_pull_t;

typedef enum {
    GPIO_IRQ_BOTH_RISING_FALLING,
    GPIO_IRQ_RISING,
    GPIO_IRQ_FALLING,
    GPIO_IRQ_LEVEL,
} meson_gpio_irq_config_edge_t;

typedef enum {
	GPIO_IRQ_FILTER_0NS      = 0,
	GPIO_IRQ_FILTER_333NS    = 1,
	GPIO_IRQ_FILTER_666NS    = 2,
	GPIO_IRQ_FILTER_999NS    = 3,
    GPIO_IRQ_FILTER_1332NS   = 4,
    GPIO_IRQ_FILTER_1665NS   = 5,
    GPIO_IRQ_FILTER_1998NS   = 6,
    GPIO_IRQ_FILTER_2331NS   = 7
} meson_gpio_irq_config_filter_t;

#define GPIO_IRQ_FILTER_2600NS 1  // only this and 0NS are used for AO channel (it is represented as value 1 as well)
