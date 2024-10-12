/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>


/*
================================================================================
================================= PPC LABELS  ==================================
================================================================================
*/

// REQUEST

#define GET_GPIO         (0)
#define SET_GPIO         (1)
#define GET_IRQ          (2)
#define SET_IRQ          (3)

// RESPONSE

#define SUCCESS          (0)
#define FAILURE          (1)

/*
================================================================================
================================= PPC FORMAT  ==================================
================================================================================
*/

/* GPIO CONTROL ARGUEMENTS */

// REQUEST
#define REQ_GPIO_CONFIG_SLOT          (0) // the function
#define REQ_GPIO_VALUE_SLOT           (1) // only use in SET requests

// RESPONSE
#define RES_GPIO_VALUE_SLOT           (0) // only used in GET requests

/* IRQ CONTROL ARGUEMENTS */

// REQUEST
#define REQ_IRQ_CONFIG_SLOT           (0) // the function
#define REQ_IRQ_VALUE_SLOT            (1) // only use in SET requests

// RESPONSE
#define RES_IRQ_VALUE_SLOT            (0) // only used in GET requests

// ERROR RESPONSE
#define RES_GPIO_IRQ_ERROR_SLOT       (0) //  used in all requests

/*
================================================================================
============================ PPC MESSAGE ARGUEMENTS  ===========================
================================================================================
*/

/* ERROR  ARGUEMENTS */

typedef enum {
    INVALID_NUM_ARGS,
    INVALID_LABEL,
    INVALID_CONFIG,
    INVALID_VALUE,
    INVALID_PIN_CONFIG_ENTRY,
    INVALID_CHANNEL_CONFIG_ENTRY
} gpio_irq_error_t;

/* GPIO CONTROL ARGUEMENTS */

typedef enum {
    OUTPUT = 0,
    INPUT,
    DIRECTION,
    GPIO_CONFIG_PLATFORM_SPECIFIC_START  // Marker for platform-specific commands
} gpio_config_t;

typedef enum {
    DIRECTION_OUTPUT,
    DIRECTION_INPUT,
} gpio_config_direction_t;

/* IRQ CONTROL ARGUEMENTS */

typedef enum {
    PIN,
    IRQ_CONFIG_PLATFORM_SPECIFIC_START  // Marker for platform-specific commands
} irq_config_t;
