/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>

#define UDP_ECHO_PORT 1235
#define UTILIZATION_PORT 1236
#define TCP_ECHO_PORT 1237

int setup_udp_socket(void);
int setup_utilization_socket(void *cycle_counters, sddf_channel start_ch, sddf_channel stop_ch);
int setup_tcp_socket(void);
