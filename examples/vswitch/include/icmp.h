/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>
#include "lwip/err.h"
#include "lwip/ip_addr.h"

#define PING_DATA_SIZE (32)

typedef struct icmp_context {
    uint32_t ip_addr;
    uint16_t seq_num;
    bool pinged;
    bool reply_received;
} icmp_context_t;

void icmp_init_raw();
bool send_icmp_request(icmp_context_t *ctx, uint8_t client_id);
