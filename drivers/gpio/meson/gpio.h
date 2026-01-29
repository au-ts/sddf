/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/gpio/protocol.h>
#include <sddf/gpio/config.h>

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
    MESON_GPIO_AO       = 0,
    MESON_GPIO_Z        = 12,
    MESON_GPIO_H        = 28,
    MESON_GPIO_BOOT     = 37,
    MESON_GPIO_C        = 53,
    MESON_GPIO_A        = 61,
    MESON_GPIO_X        = 77,
    MESON_GPIO_E        = 97,
    MESON_GPIO_TEST_N   = 100,
    MESON_GPIO_ERROR_INVALID_PIN = MESON_GPIO_PIN_COUNT
} meson_gpio_bank_t;

// we use channels 52 - 61 in the driver for device <=> driver irqs
#define MESON_GPIO_IRQ_CHANNEL_START 52
#define MESON_GPIO_IRQ_CHANNEL_COUNT 10

// these are the PREDFINED values used for device <=> driver communiation
typedef enum {
    MESON_GPIO_IRQ_0 = MESON_GPIO_IRQ_CHANNEL_START,
    MESON_GPIO_IRQ_1,
    MESON_GPIO_IRQ_2,
    MESON_GPIO_IRQ_3,
    MESON_GPIO_IRQ_4,
    MESON_GPIO_IRQ_5,
    MESON_GPIO_IRQ_6,
    MESON_GPIO_IRQ_7,
    MESON_GPIO_AO_IRQ_0,
    MESON_GPIO_AO_IRQ_1,
} meson_gpio_irq_t;

/*
================================================================================
===============================  CONFIGURATIONS  ===============================
================================================================================
*/

// typedef enum {
//     MESON_GPIO_PULL = SDDF_GPIO_PLATFORM_SPECIFIC_START,
//     MESON_GPIO_DRIVE_STRENGTH,
// } meson_gpio_config_t;

// typedef enum {
//     MESON_GPIO_IRQ_EDGE = GPIO_IRQ_CONFIG_PLATFORM_SPECIFIC_START,
//     MESON_GPIO_IRQ_FILTER,
// } meson_gpio_irq_config_t;

/*
================================================================================
===================================  VALUES  ===================================
================================================================================
*/

typedef enum {
	MESON_GPIO_DS_500UA    = 0,
	MESON_GPIO_DS_2500UA   = 1,
	MESON_GPIO_DS_3000UA   = 2,
	MESON_GPIO_DS_4000UA   = 3,
} meson_gpio_config_drv_str_t;

typedef enum {
    MESON_GPIO_PULL_UP,
    MESON_GPIO_PULL_DOWN,
    MESON_GPIO_NO_PULL,
} meson_gpio_config_pull_t;

typedef enum {
    MESON_GPIO_IRQ_BOTH_RISING_FALLING,
    MESON_GPIO_IRQ_RISING,
    MESON_GPIO_IRQ_FALLING,
    MESON_GPIO_IRQ_LEVEL,
} meson_gpio_irq_config_edge_t;

typedef enum {
	MESON_GPIO_IRQ_FILTER_0NS      = 0,
	MESON_GPIO_IRQ_FILTER_333NS    = 1,
	MESON_GPIO_IRQ_FILTER_666NS    = 2,
	MESON_GPIO_IRQ_FILTER_999NS    = 3,
    MESON_GPIO_IRQ_FILTER_1332NS   = 4,
    MESON_GPIO_IRQ_FILTER_1665NS   = 5,
    MESON_GPIO_IRQ_FILTER_1998NS   = 6,
    MESON_GPIO_IRQ_FILTER_2331NS   = 7
} meson_gpio_irq_config_filter_t;

#define MESON_GPIO_IRQ_FILTER_2600NS 1  // only this and 0NS are used for AO channel (it is represented as value 1 as well)
