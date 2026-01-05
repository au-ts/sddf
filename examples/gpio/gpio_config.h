/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdio.h>
#include <sddf/gpio/meson/gpio.h>
#include <sddf/gpio/imx/gpio.h>

// Right motor pins
#define GPIO_1 (MESON_GPIO_X + 1)
// #define GPIO_2 (MESON_GPIO_X + 2)

// Left motor pins
// #define GPIO_3 (MESON_GPIO_X + 3)
// #define GPIO_4 (MESON_GPIO_X + 4)

// WARNING : The GPIOA pins DO NOT work for input!!

#define GPIO_CHANNEL_MAPPING_COLS   3  // do not change
#define GPIO_CHANNEL_MAPPING_ROWS   62 // do not change

/* channel number for client <=> driver interaction, from driver perspective */
#define GPIO_CHANNEL_MAPPING_CLIENTS_CHANNEL_SLOT           0
/* which gpio pin its for */
#define GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT                  1
/* which device irq channel its for (driver perspective) */
#define GPIO_CHANNEL_MAPPING_IRQ_SLOT               2

/*
- GPIO Pin entries must use the scheme inside of sddf/include/gpio/{platform}/gpio.h.
- IRQ Channel entries must use the scheme inside of sddf/include/gpio/{platform}/gpio.h.
- Unused fields must be initialised to -1.
- If a channel is used for device <=> driver communication leave it uninitialised here
    For example if theres entry { 1, GPIO_2, GPIO_IRQ_0}, then you must have the entry { 52, -1, -1 },
    because channel 52 is for GPIO_IRQ_0.
*/
static const int gpio_channel_mappings[GPIO_CHANNEL_MAPPING_ROWS][GPIO_CHANNEL_MAPPING_COLS] = {
    { 0, GPIO_1, -1 },
    { 1, -1, -1 },
    { 2, -1, -1 },
    { 3, -1, -1 },
    { 4, -1, -1 },
    { 5, -1, -1 },
    { 6, -1, -1 },
    { 7, -1, -1 },
    { 8, -1, -1 },
    { 9, -1, -1 },
    { 10, -1, -1 },
    { 11, -1, -1 },
    { 12, -1, -1 },
    { 13, -1, -1 },
    { 14, -1, -1 },
    { 15, -1, -1 },
    { 16, -1, -1 },
    { 17, -1, -1 },
    { 18, -1, -1 },
    { 19, -1, -1 },
    { 20, -1, -1 },
    { 21, -1, -1 },
    { 22, -1, -1 },
    { 23, -1, -1 },
    { 24, -1, -1 },
    { 25, -1, -1 },
    { 26, -1, -1 },
    { 27, -1, -1 },
    { 28, -1, -1 },
    { 29, -1, -1 },
    { 30, -1, -1 },
    { 31, -1, -1 },
    { 32, -1, -1 },
    { 33, -1, -1 },
    { 34, -1, -1 },
    { 35, -1, -1 },
    { 36, -1, -1 },
    { 37, -1, -1 },
    { 38, -1, -1 },
    { 39, -1, -1 },
    { 40, -1, -1 },
    { 41, -1, -1 },
    { 42, -1, -1 },
    { 43, -1, -1 },
    { 44, -1, -1 },
    { 45, -1, -1 },
    { 46, -1, -1 },
    { 47, -1, -1 },
    { 48, -1, -1 },
    { 49, -1, -1 },
    { 50, -1, -1 },
    { 51, -1, -1 },
    { 52, -1, -1 },
    { 53, -1, -1 },
    { 54, -1, -1 },
    { 55, -1, -1 },
    { 56, -1, -1 },
    { 57, -1, -1 },
    { 58, -1, -1 },
    { 59, -1, -1 },
    { 60, -1, -1 },
    { 61, -1, -1 },
};
