/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#ifndef IPERF3_CTRL_H
#define IPERF3_CTRL_H

#include <stdint.h>
#include <stdbool.h>
#include "lwip/tcp.h"
#include "lwip/ip_addr.h"

#include "iperf3_stream.h"

#define IPERF3_COOKIE_LEN 37
#define MAX_STREAMS 15
#define PAYLOAD_SIZE 16384

typedef enum {
    CTRL_WAIT_STATE,    /* 1-byte state from server */
    CTRL_WAIT_JSON_LEN, /* 4-byte JSON length field from server */
    CTRL_WAIT_JSON_BODY,/* JSON body from server */
} ctrl_rx_phase_t;

typedef struct iperf_ctrl {
    struct tcp_pcb *pcb;
    uint8_t cookie[IPERF3_COOKIE_LEN];

    /* iperf3 server port (control + data), from the injected app config */
    uint16_t server_port;

    iperf3_stream_t streams[MAX_STREAMS];         /* TCP data streams */
    iperf3_udp_stream_t udp_streams[MAX_STREAMS]; /* UDP data streams */

    ctrl_rx_phase_t rx_phase;
    uint8_t server_state;
    uint32_t json_len;
    uint32_t json_rx;

    uint8_t json_len_buf[4];
    uint8_t json_len_rx;
    uint8_t payload[PAYLOAD_SIZE];
    uint8_t result_json[65536];

    uint8_t num_streams;
    uint64_t bytes_sent;

    /* TCP control-channel tx state */
    const int8_t *tx_buf;
    uint16_t tx_len;
    uint16_t tx_off;

    bool test_done;
    bool test_active;
    bool sent_test_end;

    /* TCP-only: result JSON built at EXCHANGE_RESULTS */
    double cpu_util_percent;
    char json_send_buf[512];

    uint32_t omit_ms;
    uint32_t omit_end_ms;
    bool omitting;

    uint32_t duration_ms;
    uint32_t end_time_ms;

    /* Runtime test parameters, set from the serial `start` command before the
     * control connection is opened (see iperf3_begin_test in iperf3_client.c).
     * These drive the param-exchange JSON and the per-stream rate limiting,
     * replacing the old compile-time NUM_STREAMS / TARGET_BW_MBPS macros. */
    uint32_t duration_s;     /* test duration in seconds */
    uint32_t omit_s;         /* warm-up (omit) seconds, excluded from results */
    uint32_t target_bw_mbps; /* per-test rate target, 0 = unlimited */
    uint16_t payload_len;    /* UDP datagram payload length (bytes) */
    char param_json[256];    /* built param-exchange JSON */
} iperf_ctrl_t;

void iperf3_ctrl_init(iperf_ctrl_t *ctrl);
err_t iperf_ctrl_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err);
err_t iperf_ctrl_sent(void *arg, struct tcp_pcb *tpcb, u16_t len);
void iperf3_ctrl_err(void *arg, err_t err);
err_t iperf_ctrl_connect(void *arg, struct tcp_pcb *pcb, err_t err);
void iperf3_on_timer_tick(iperf_ctrl_t *ctrl, uint32_t now_ms);
void iperf3_tcp_check_deadline(iperf_ctrl_t *ctrl, uint32_t now_ms);
void iperf3_tcp_rtt_aggregate(iperf_ctrl_t *ctrl, uint32_t *o_min, uint32_t *o_mean,
                              uint32_t *o_max, uint32_t *o_sd, uint64_t *o_n);

#endif
