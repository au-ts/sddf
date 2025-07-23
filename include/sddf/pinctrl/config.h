/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <os/sddf.h>
#include <stdbool.h>
#include <stdint.h>

#define SDDF_PINCTRL_MAX_CLIENTS 64
#define SDDF_PINCTRL_MAGIC_LEN 5
static char SDDF_PINCTRL_MAGIC[SDDF_PINCTRL_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x8 };

typedef struct pinctrl_client_config {
    char magic[SDDF_PINCTRL_MAGIC_LEN];
    uint8_t driver_id;
} pinctrl_client_config_t;

static bool pinctrl_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_PINCTRL_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_PINCTRL_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
