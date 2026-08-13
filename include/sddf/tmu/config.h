/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <os/sddf.h>
#include <stdbool.h>
#include <stdint.h>

#define SDDF_TMU_MAX_CLIENTS 64
#define SDDF_TMU_MAGIC_LEN 4
static char SDDF_TMU_MAGIC[SDDF_TMU_MAGIC_LEN] = { 'T', 'M', 'U', 0x2 };

typedef struct tmu_client_config {
    char magic[SDDF_TMU_MAGIC_LEN];
    uint8_t driver_id;
} tmu_client_config_t;

typedef struct tmu_driver_config {
    char magic[SDDF_TMU_MAGIC_LEN];
    uint8_t controller_channel;
    bool do_irq_fwd;
} tmu_driver_config_t;

static inline bool tmu_config_check_magic(void *config)
{
    char *magic = (char *)config;
    for (int i = 0; i < SDDF_TMU_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_TMU_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
