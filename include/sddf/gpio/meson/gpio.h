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

/*
================================================================================
===================================  CONVERSIONS  ==============================
================================================================================
*/

// PIN NUMBER = BANK NAME + BANK PIN NUMBER

#define MESON_GPIO_PIN_COUNT 101
#define MESON_GPIO_BANK_COUNT 9

typedef enum {
    GPIO_AO = 0,
    GPIO_Z = 12,
    GPIO_H = 28,
    BOOT = 37,
    GPIO_C = 53,
    GPIO_A = 61,
    GPIO_X = 77,
    GPIO_E = 97,
    TEST_N = 100,
    ERROR_INVALID_PIN = MESON_GPIO_PIN_COUNT
} meson_gpio_bank_t;

typedef enum {
    GPIO_IRQ_0 = 0,
    GPIO_IRQ_1,
    GPIO_IRQ_2,
    GPIO_IRQ_3,
    GPIO_IRQ_4,
    GPIO_IRQ_5,
    GPIO_IRQ_6,
    GPIO_IRQ_7,
    GPIO_AO_IRQ_0 = 8,
    GPIO_AO_IRQ_1,
    MESON_IRQ_CHANNEL_COUNT
} meson_irq_gpio_t;


/*
================================================================================
=================================  FUNCTIONS  ==================================
================================================================================
*/

typedef enum {
    PULL = GPIO_CONFIG_PLATFORM_SPECIFIC_START,
    DRIVE_STRENGTH,
    // AO_LOCK, - not implemented
} meson_gpio_config_t;

typedef enum {
    EDGE = IRQ_CONFIG_PLATFORM_SPECIFIC_START,
    FILTER,
    // AO_FILTER_USE_CLK, - not implemented
} meson_irq_config_t;

typedef enum {
	DS_500UA = 0,
	DS_2500UA = 1,
	DS_3000UA = 2,
	DS_4000UA = 3,
} meson_gpio_config_drv_str_t;

typedef enum {
    PULL_UP,
    PULL_DOWN,
    NO_PULL,
} meson_gpio_config_pull_t;

// typedef enum { - not implemented
//     LOCK,
//     UNLOCK,
// } gpio_meson_config_ao_lock_t;

typedef enum {
    BOTH_RISING_FALLING,
    RISING,
    FALLING,
    LEVEL,
} meson_irq_config_edge_t;

// typedef enum { - not implemented
//     ENABLE,
//     DISABLE,
// } meson_irq_config_ao_filter_use_clk_t;

typedef enum {
	FILTER_0NS = 0,
	FILTER_333NS = 1,
	FILTER_666NS = 2,
	FILTER_999NS = 3,
    FILTER_1332NS = 4,
    FILTER_1665NS = 5,
    FILTER_1998NS = 6,
    FILTER_2331NS = 7,
    FILTER_2600NS           // only this and 0NS are used for AO channel (it is represented as value 1 as well)
} meson_irq_config_filter_t;

