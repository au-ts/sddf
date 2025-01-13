/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <microkit.h>

#define SDDF_TIMER_MAX_CLIENTS (MICROKIT_MAX_CHANNELS - 1)

typedef struct timer_client_config {
    uint8_t driver_id;
} timer_client_config_t;
