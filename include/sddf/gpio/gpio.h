/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

#if defined(CONFIG_PLAT_ODROIDC4)
#define GPIO_PIN_COUNT                       MESON_GPIO_PIN_COUNT
#define IRQ_CHANNEL_COUNT                    MESON_IRQ_CHANNEL_COUNT
#else
#error "Must define GPIO_PIN_COUNT and IRQ_CHANNEL_COUNT for security lists in virtualiser"
#endif

/*
================================================================================
================================= PPC LABELS  ==================================
================================================================================
*/

// REQUEST

#define GPIO_PIN_CLAIM           (1)
#define GPIO_PIN_RELEASE         (2)
#define IRQ_CHANNEL_CLAIM        (3)
#define IRQ_CHANNEL_RELEASE      (4)

#define GET_GPIO_CONFIG          (5)
#define SET_GPIO_CONFIG          (6)
#define GET_IRQ_CONFIG           (7)
#define SET_IRQ_CONFIG           (8)

// RESPONSE

#define SUCCESS                  (0)
#define FAILURE                  (1)

/*
================================================================================
=============================== PPC ARGUEMENTS  ================================
================================================================================
*/

typedef enum {
    INVALID_PERMISSION,
    INVALID_PIN_ALREADY_CLAIMED,
    INVALID_NUM_ARGS,
    INVALID_LABEL,
    INVALID_CONFIG,
    INVALID_VALUE,
    INVALID_PIN,
    INVALID_CHANNEL,
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
} rq_config_t;

/*
================================================================================
================================= PPC FORMAT  ==================================
================================================================================
*/

/* GPIO CONTROL ARGUEMENTS */

// REQUEST
#define REQ_GPIO_PIN_SLOT             (0) // linear scheme (determined by platform header)
#define REQ_GPIO_CONFIG_SLOT          (1) // the function
#define REQ_GPIO_VALUE_SLOT           (2) // only use in SET requests

// RESPONSE
#define RES_GPIO_VALUE_SLOT           (0) // only used in GET requests

/* IRQ CONTROL ARGUEMENTS */

// REQUEST
#define REQ_IRQ_CHANNEL_SLOT          (0) // linear scheme (determined by platform header)
#define REQ_IRQ_CONFIG_SLOT           (1) // the function
#define REQ_IRQ_VALUE_SLOT            (2) // only use in SET requests

// RESPONSE
#define RES_IRQ_VALUE_SLOT            (0) // only usee in GET requests

// ERROR RESPONSE
#define RES_GPIO_IRQ_ERROR_SLOT       (0)