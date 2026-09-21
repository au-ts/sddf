/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>

extern __attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;
extern serial_queue_handle_t rx_queue_handle;
extern serial_queue_handle_t tx_queue_handle;
