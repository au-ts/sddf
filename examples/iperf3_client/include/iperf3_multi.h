#pragma once

#include <stdint.h>

/* Multi-client test coordination */

#define IPERF3_SHARED_PARAMS_VADDR 0x30000000UL

#define IPERF3_MAX_PEERS 4

/* Injected at link time into .iperf3_multi_config, one per copied client ELF */
typedef struct iperf3_multi_config {
    uint8_t is_controller;                    /* 1 for client0, 0 for peers */
    uint8_t num_peers;                        /* controller: number of peers */
    uint8_t listen_channel;                   /* peer: channel the controller pokes */
    uint8_t peer_channels[IPERF3_MAX_PEERS];  /* controller: channels to notify */
} iperf3_multi_config_t;

/* Lives in the shared region at IPERF3_SHARED_PARAMS_VADDR */
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
    uint32_t is_reverse;
    uint32_t is_bidirectional;
} iperf3_shared_params_t;
