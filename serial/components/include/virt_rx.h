/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>

#define MAX_CLI_BASE_10 4

extern serial_queue_handle_t rx_queue_handle_drv;
extern serial_queue_handle_t rx_queue_handle_cli[SDDF_SERIAL_MAX_CLIENTS];
extern char next_client[MAX_CLI_BASE_10 + 1];
extern __attribute__((__section__(".serial_virt_rx_config"))) serial_virt_rx_config_t config;
