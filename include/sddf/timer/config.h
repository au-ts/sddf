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

typedef struct {
    char magic[SDDF_TIMER_MAGIC_LEN + 1];
    uint8_t virt_id;
} timer_driver_config_t;

typedef struct timer_client_config {
    char magic[SDDF_TIMER_MAGIC_LEN + 1];
    uint8_t virt_id;
    uint64_t req_vaddr;
} timer_client_config_t;

typedef struct {
    char magic[SDDF_TIMER_MAGIC_LEN + 1];
    uint8_t driver_id;
    // NOTE: indexed by channel, zero unused channels
    uint64_t req_vaddrs[SDDF_TIMER_MAX_CLIENTS];
} sddf_timer_virt_config_t;

static inline bool timer_config_check_magic(const void *config)
{
    const char *magic = (const char *)config;
    for (int i = 0; i < SDDF_TIMER_MAGIC_LEN; i++) {
        if (magic[i] != SDDF_TIMER_MAGIC[i]) {
            return false;
        }
    }

    return true;
}
