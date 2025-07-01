/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <os/sddf.h>
#include <stdbool.h>
#include <stdint.h>

#define MAX_CHANNELS 62
#define SDDF_GPIO_MAGIC_LEN 5
static char SDDF_GPIO_MAGIC[SDDF_GPIO_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x8 };

typedef struct gpio_client_config {
    char magic[SDDF_GPIO_MAGIC_LEN];
    uint8_t num_driver_channel_ids;
    uint8_t driver_channel_ids[MAX_CHANNELS];
} gpio_client_config_t;

static bool gpio_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_GPIO_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_GPIO_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
