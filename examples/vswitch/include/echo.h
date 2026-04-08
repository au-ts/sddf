/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>

#define UDP_ECHO_PORT 1235
#define TCP_ECHO_PORT 1236
#define UTILIZATION_PORT 1237

#define TCP_ECHO_MAX_CONNS 4

typedef struct vswitch_client_config {
    uint8_t channel_id;
} vswitch_client_config_t;

int setup_udp_socket(void);
int setup_utilization_socket(void *benchmark_config);
int setup_tcp_socket(void);
