/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>

/* Multi-client test coordination.
 *
 * In a multi-client build (e.g. four_core: client0 + client1) only client0
 * receives serial input (serial_virt_rx routes keystrokes to one client). So
 * client0 acts as the *controller*: when you type a `start` command it writes
 * the parsed parameters into a shared memory region and notifies each peer
 * client over a dedicated channel. Each peer then runs the SAME test against
 * its own server port (base_port + client_id), so all clients benchmark
 * concurrently with identical parameters.
 *
 * NOTE: this relies on cross-core asynchronous notifications, which do not work
 * under QEMU SMP (see CLAUDE.md) but do on real hardware.
 */

/* Fixed virtual address where the shared params region is mapped into every
 * client PD (see meta.py add_map). */
#define IPERF3_SHARED_PARAMS_VADDR 0x30000000UL

/* Upper bound on peer clients a controller can notify (client1..clientN). */
#define IPERF3_MAX_PEERS 8

/* Injected at link time into .iperf3_multi_config, one per copied client ELF.
 * Layout must match IperfMultiConfig.serialise() in meta.py ("<BBB8s"). */
typedef struct iperf3_multi_config {
    uint8_t is_controller;                    /* 1 for client0, 0 for peers */
    uint8_t num_peers;                        /* controller: number of peers */
    uint8_t listen_channel;                   /* peer: channel the controller pokes */
    uint8_t peer_channels[IPERF3_MAX_PEERS];  /* controller: channels to notify */
} iperf3_multi_config_t;

/* Lives in the shared region at IPERF3_SHARED_PARAMS_VADDR. The controller
 * writes it (params first, `generation` last) and notifies peers; each peer
 * reads it on notification and treats a changed `generation` as a new test. */
typedef struct iperf3_shared_params {
    uint32_t generation;     /* bumped by controller per new test */
    uint8_t  server_ip[4];   /* server IPv4 */
    uint16_t base_port;      /* client i targets base_port + i */
    uint8_t  is_udp;         /* protocol for this test (0 = TCP, 1 = UDP) */
    uint8_t  _pad;
    uint32_t duration_s;
    uint32_t num_streams;
    uint32_t bw_mbps;        /* 0 = unlimited */
    uint32_t payload_len;    /* UDP datagram bytes */
} iperf3_shared_params_t;
