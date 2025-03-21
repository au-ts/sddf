/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <os/sddf.h>
#include <stdbool.h>
#include <stdint.h>

#define SDDF_TIMER_MAX_CLIENTS 64
#define SDDF_TIMER_MAGIC_LEN 5
static char SDDF_TIMER_MAGIC[SDDF_TIMER_MAGIC_LEN] = { 's', 'D', 'D', 'F', 0x6 };

typedef struct timer_client_config {
    char magic[SDDF_TIMER_MAGIC_LEN];
    uint8_t driver_id;
} timer_client_config_t;

static bool timer_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_TIMER_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_TIMER_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
