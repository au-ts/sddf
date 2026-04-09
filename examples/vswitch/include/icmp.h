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

// TODO: later construct the struct for sharing the state for replies
typedef struct icmp_context {
    uint32_t ip_addr;
    uint16_t seq_num;
} icmp_context_t;

void icmp_init_raw();
bool send_icmp_request(icmp_context_t *ctx);
