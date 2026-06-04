/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>

/* Per-client application config injected at link time into the
 * .iperf3_app_config section. Because the client ELF is copied once per
 * client (client0, client1, ...), this lets each copy target a different
 * iperf3 server port without recompiling. Populated by meta.py. */
typedef struct iperf3_app_config {
    uint8_t server_ip[4];   /* server IPv4 address, e.g. {10,0,2,2} */
    uint16_t server_port;   /* iperf3 server control/data port (0 => default 5202) */
    uint8_t client_id;      /* 0, 1, ... for logging */
} iperf3_app_config_t;
