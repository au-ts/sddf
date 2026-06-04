/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#ifndef IPERF3_STREAM_H
#define IPERF3_STREAM_H

#include <stdint.h>
#include <stdbool.h>
#include "lwip/tcp.h"
#include "lwip/udp.h"
#include "lwip/ip_addr.h"

struct iperf_ctrl;
typedef struct iperf_ctrl iperf_ctrl_t;

typedef enum {
    COOKIE_SEND,
    MESSAGE_SEND,
    SEND_PAYLOAD,
    STOPPED
} stream_phase_t;

/* TCP stream */
typedef struct {
    struct tcp_pcb *pcb;
    uint8_t *cookie;

    uint64_t bytes;
    const uint8_t *tx_buf;

    uint16_t tx_len;
    uint16_t tx_off;
    stream_phase_t phase;

    uint32_t bytes_this_tick;
    uint32_t tick_byte_limit;   /* 0 = unlimited */

    /* Self-measured RTT (microseconds) via ACK round-trips. lwIP's own RTT
     * estimate is 500ms-granular (useless for LAN), so we time one outstanding
     * sample at a time: record send time at a byte offset, complete when that
     * offset is ACKed. min/max/mean/stddev need no sample storage. */
    uint64_t rtt_sent;      /* cumulative bytes handed to tcp_write */
    uint64_t rtt_acked;     /* cumulative bytes ACKed */
    uint64_t rtt_target;    /* byte offset of the sample being timed */
    uint64_t rtt_t0_ns;     /* send time of that byte */
    bool     rtt_pending;   /* a sample is in flight */
    uint32_t rtt_min_us, rtt_max_us, rtt_count;
    uint64_t rtt_sum_us, rtt_sumsq_us;

    iperf_ctrl_t *ctrl;
} iperf3_stream_t;

/* UDP stream */
typedef struct {
    struct udp_pcb *pcb;
    ip_addr_t server_addr;
    uint16_t server_port;
    uint64_t packets_sent;
    uint64_t bytes_sent;
    uint32_t seq_num;

    const uint8_t *tx_buf;
    stream_phase_t phase;
    uint16_t payload_len;
    uint32_t burst_max;
    uint32_t packets_this_tick;
    iperf_ctrl_t *ctrl;
} iperf3_udp_stream_t;

/* TCP stream functions */
void iperf3_stream_init(iperf3_stream_t *stream, uint8_t *cookie, iperf_ctrl_t *ctrl);
void iperf3_stream_maybe_tx(iperf3_stream_t *stream);
err_t iperf3_stream_connect(void *arg, struct tcp_pcb *pcb, err_t err);
err_t iperf3_stream_sent(void *arg, struct tcp_pcb *tpcb, u16_t len);
err_t iperf3_stream_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err);
void iperf3_stream_err(void *arg, err_t err);

/* UDP stream functions */
void udp_pump(iperf3_udp_stream_t *stream);
void udp_stream_recv(void *arg, struct udp_pcb *pcb, struct pbuf *p,
                     const ip_addr_t *addr, u16_t port);

#endif // IPERF3_STREAM_H
