/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#define UDP_ECHO_PORT 1235
#define UTILIZATION_PORT 1236
#define TCP_ECHO_PORT 1237

#define LINK_SPEED 1000000000 // Gigabit
#define ETHER_MTU 1500

int setup_udp_socket(void);
int setup_utilization_socket(void);
int setup_tcp_socket(void);
