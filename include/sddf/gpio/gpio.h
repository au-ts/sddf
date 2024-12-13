/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

/* COMMON FORMAT FOR GPIO PPC REQUESTS/RESPONSES */

/*
================================================================================
================================== LABEL  ======================================
================================================================================
*/

/* REQUEST */
#define GPIO_GET_GPIO         (0)
#define GPIO_SET_GPIO         (1)
#define GPIO_GET_IRQ          (2)
#define GPIO_SET_IRQ          (3)

/* RESPONSE */
#define GPIO_SUCCESS          (0)
#define GPIO_FAILURE          (1)

/*
================================================================================
================================= REGISTERS  ===================================
================================================================================
*/

/* REQUEST ARGUEMENTS */
#define GPIO_REQ_CONFIG_SLOT          (0)
#define GPIO_REQ_VALUE_SLOT           (1)


/* RESPONSE ARGUEMENTS */
#define GPIO_RES_VALUE_SLOT           (0)

/*
================================================================================
============================ PPC MESSAGE ARGUEMENTS  ===========================
================================================================================
*/

/* ERROR ARGUEMENTS */

typedef enum {
    GPIO_INVALID_NUM_ARGS,
    GPIO_INVALID_LABEL,
    GPIO_INVALID_CONFIG,
    GPIO_INVALID_VALUE,
    GPIO_INVALID_PIN_CONFIG_ENTRY,
    GPIO_INVALID_CHANNEL_CONFIG_ENTRY,
    GPIO_INVALID_MAPPING_ENTRY
} gpio_error_t;

/* GPIO CONTROL ARGUEMENTS */

typedef enum {
    GPIO_OUTPUT = 0,
    GPIO_INPUT,
    GPIO_DIRECTION,
    GPIO_CONFIG_PLATFORM_SPECIFIC_START  // Marker for platform-specific commands
} gpio_config_t;

typedef enum {
    GPIO_DIRECTION_OUTPUT,
    GPIO_DIRECTION_INPUT,
} gpio_config_direction_t;

/* GPIO IRQ CONTROL ARGUEMENTS */

typedef enum {
    GPIO_IRQ_PIN,
    GPIO_IRQ_CONFIG_PLATFORM_SPECIFIC_START  // Marker for platform-specific commands
} gpio_irq_config_t;
