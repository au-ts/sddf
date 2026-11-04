/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>

#define TX_PENDING_MAX (SDDF_SERIAL_MAX_CLIENTS + 1)
typedef struct tx_pending {
    uint32_t queue[TX_PENDING_MAX];
    bool clients_pending[SDDF_SERIAL_MAX_CLIENTS];
    uint32_t head;
    uint32_t tail;
} tx_pending_t;

#define COLOUR_BEGIN_LEN 5
#define COLOUR_END "\x1b[0m"
#define COLOUR_END_LEN 4

extern __attribute__((__section__(".serial_virt_tx_config"))) serial_virt_tx_config_t config;
extern const char *colours[6];
extern serial_queue_handle_t tx_queue_handle_drv;
extern serial_queue_handle_t tx_queue_handle_cli[SDDF_SERIAL_MAX_CLIENTS];
extern tx_pending_t tx_pending;
