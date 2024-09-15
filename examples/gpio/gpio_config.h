/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#ifndef GPIO_CONFIG_H
#define GPIO_CONFIG_H

#include <stdio.h>
#include <sddf/gpio/meson/gpio.h>

#define GPIO_1 (GPIO_H + 5)
#define GPIO_2 (GPIO_X + 4)

/*
================================================================================
================================== IRQ CHANNELS  ===============================
================================================================================
*/

/* Device <-> Driver GPIO IRQ channels */
/* Must be linear, skip numbers and be in this order */
#define DEV_GPIO_IRQ_0_CH       53
#define DEV_GPIO_IRQ_1_CH       54
#define DEV_GPIO_IRQ_2_CH       55
#define DEV_GPIO_IRQ_3_CH       56
#define DEV_GPIO_IRQ_4_CH       57
#define DEV_GPIO_IRQ_5_CH       58
#define DEV_GPIO_IRQ_6_CH       59
#define DEV_GPIO_IRQ_7_CH       60
#define DEV_AO_GPIO_IRQ_0_CH    61
#define DEV_AO_GPIO_IRQ_1_CH    62

#define DEV_IRQ_CHANNEL_OFFSET DEV_GPIO_IRQ_0_CH

/*
================================================================================
================================== GPIO CHANNELS  ==============================
================================================================================
*/

#define NUM_CLI_GPIO_CHANNELS (63-10)
#define EXPECTED_SIZE (NUM_CLI_GPIO_CHANNELS * sizeof(int[3]))

#define CHANNEL_MAPPINGS_CHANNEL_NUMBER_INDEX 0
#define CHANNEL_MAPPINGS_GPIO_PIN_INDEX 1
#define CHANNEL_MAPPINGS_DEV_IRQ_CHANNEL_INDEX 2

/*
- Channel Mappings must not skip any channel numbers between 0 and up to last channel defined above.
- Pins must use the linear scheme inside of sddf/include/gpio/{platform}/gpio.h.
- Unused fields must be initialised to -1.
*/
extern const int channel_mappings[NUM_CLI_GPIO_CHANNELS][3] = {
    { 0, GPIO_1, -1 }, // we are using this channel but its not mapped
    { 1, GPIO_2, DEV_GPIO_IRQ_0_CH},
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
    { 52, -1, -1 }
};

#endif /* GPIO_CONFIG_H */
