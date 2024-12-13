/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

/* COMMON FORMAT FOR ALL GPIO PPC REQUESTS/RESPONSES | PLATFORM INDEPENDENT */

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
============================== ARGUEMENT POSITION  =============================
================================================================================
*/

/* REQUEST ARGUEMENTS */
#define GPIO_REQ_CONFIG_SLOT          (0)
#define GPIO_REQ_VALUE_SLOT           (1)


/* RESPONSE ARGUEMENTS */
#define GPIO_RES_VALUE_SLOT           (0)

/*
================================================================================
===================================  ERRORS  ===================================
================================================================================
*/

// TODO: go and make sure drivers use these
typedef enum {
    GPIO_ERROR_INVALID_NUM_ARGS,       // Incorrect number of arguments
    GPIO_ERROR_INVALID_LABEL,          // Incorrect GPIO label
    GPIO_ERROR_INVALID_CONFIG,         // Invalid configuration
    GPIO_ERROR_INVALID_VALUE,          // Invalid value
    GPIO_ERROR_UNSUPPORTED_PIN_CONFIG, // Requested config not supported for this pin
    GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG, // Requested config not supported for this IRQ
    GPIO_ERROR_PERMISSION_DENIED       // Operation not allowed due to config file restrictions
} gpio_error_t;

/*
================================================================================
===============================  CONFIGURATIONS  ===============================
================================================================================
*/

typedef enum {
    GPIO_OUTPUT = 0,
    GPIO_INPUT,
    GPIO_DIRECTION,
    GPIO_CONFIG_PLATFORM_SPECIFIC_START  // Marker for platform-specific commands
} gpio_config_t;

typedef enum {
    GPIO_IRQ_PIN,
    GPIO_IRQ_CONFIG_PLATFORM_SPECIFIC_START  // Marker for platform-specific commands
} gpio_irq_config_t;

/*
================================================================================
===================================  VALUES  ===================================
================================================================================
*/

typedef enum {
    GPIO_DIRECTION_OUTPUT,
    GPIO_DIRECTION_INPUT,
} gpio_config_direction_t;
