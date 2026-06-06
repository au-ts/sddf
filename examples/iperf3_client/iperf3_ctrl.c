/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <stdbool.h>
#include "lwip/tcp.h"
#include "lwip/ip.h"
#include "lwip/pbuf.h"
#include "lwip/ip_addr.h"
#include <string.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/timer/config.h>
#include <sddf/timer/client.h>
#include <lwip/udp.h>

#include "iperf3_ctrl.h"

#define PARAM_EXCHANGE   9
#define CREATE_STREAMS  10
#define TEST_START       1
#define TEST_RUNNING     2
#define TEST_END         4
#define EXCHANGE_RESULTS 13
#define DISPLAY_RESULTS  14
#define IPERF_DONE       16

#define UDP_CONNECT_MSG 0x36373839

extern timer_client_config_t timer_config;

static uint32_t read_be32(const uint8_t b[4]) {
    return ((uint32_t)b[0] << 24) |
           ((uint32_t)b[1] << 16) |
           ((uint32_t)b[2] <<  8) |
           ((uint32_t)b[3] <<  0);
}

/* Integer sqrt (avoids pulling in math.h) — used for RTT stddev. */
static uint32_t isqrt64(uint64_t x) {
    uint64_t r = 0, b = 1ULL << 62;
    while (b > x) b >>= 2;
    while (b) {
        if (x >= r + b) { x -= r + b; r = (r >> 1) + b; }
        else r >>= 1;
        b >>= 2;
    }
    return (uint32_t)r;
}

/* Aggregate self-measured RTT (us) across all TCP streams into out-params. */
void iperf3_tcp_rtt_aggregate(iperf_ctrl_t *ctrl, uint32_t *o_min, uint32_t *o_mean,
                              uint32_t *o_max, uint32_t *o_sd, uint64_t *o_n) {
    uint32_t rmin = 0xFFFFFFFFu, rmax = 0;
    uint64_t rsum = 0, rsumsq = 0, rcnt = 0;
    for (int s = 0; s < ctrl->num_streams; s++) {
        iperf3_stream_t *st = &ctrl->streams[s];
        if (!st->rtt_count) continue;
        if (st->rtt_min_us < rmin) rmin = st->rtt_min_us;
        if (st->rtt_max_us > rmax) rmax = st->rtt_max_us;
        rsum += st->rtt_sum_us;
        rsumsq += st->rtt_sumsq_us;
        rcnt += st->rtt_count;
    }
    uint32_t rmean = rcnt ? (uint32_t)(rsum / rcnt) : 0;
    *o_min  = rcnt ? rmin : 0;
    *o_mean = rmean;
    *o_max  = rmax;
    *o_sd   = rcnt ? isqrt64(rsumsq / rcnt - (uint64_t)rmean * rmean) : 0;
    *o_n    = rcnt;
}

void iperf3_ctrl_init(iperf_ctrl_t *ctrl) {
    ctrl->pcb = NULL;
    memset(ctrl->cookie, 0, IPERF3_COOKIE_LEN);
    ctrl->rx_phase = CTRL_WAIT_STATE;
    ctrl->server_state = 0;
    ctrl->json_len = 0;
    ctrl->json_rx = 0;
    ctrl->json_len_rx = 0;
    ctrl->sent_test_end = false;
    ctrl->test_active = false;
    ctrl->test_done = false;
    ctrl->bytes_sent = 0;
    ctrl->omitting = false;
    /* Sane defaults; the serial `start` command overrides these in
     * iperf3_begin_test() before the control connection is opened. */
    ctrl->num_streams = 1;
    ctrl->target_bw_mbps = 0;
    ctrl->payload_len = 1460;
    ctrl->is_udp = false;
    ctrl->duration_s = 10;
    ctrl->omit_s = 5;
    for (int i = 0; i < MAX_STREAMS; i++) {
        ctrl->streams[i].pcb = NULL;
        ctrl->streams[i].bytes = 0;
        ctrl->streams[i].phase = STOPPED;
    }
}

static void iperf3_ctrl_maybe_tx(iperf_ctrl_t *ctrl) {
    if (ctrl->pcb == NULL) return;
    if (ctrl->tx_len == ctrl->tx_off) return;
    u16_t avail = tcp_sndbuf(ctrl->pcb);
    if (avail == 0) return;
    u16_t remaining = ctrl->tx_len - ctrl->tx_off;
    u16_t chunk = remaining > avail ? avail : remaining;
    err_t err = tcp_write(ctrl->pcb, ctrl->tx_buf + ctrl->tx_off, chunk, TCP_WRITE_FLAG_COPY);
    if (err != ERR_OK) return;
    ctrl->tx_off += chunk;
    tcp_output(ctrl->pcb);
}

static err_t iperf_set_send_state(iperf_ctrl_t *ctrl, signed int state) {
    ctrl->server_state = state;
    ctrl->tx_buf = (const int8_t *)&ctrl->server_state;
    ctrl->tx_len = 1;
    ctrl->tx_off = 0;
    iperf3_ctrl_maybe_tx(ctrl);
    return ERR_OK;
}

err_t iperf_ctrl_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err) {
    iperf_ctrl_t *ctrl = (iperf_ctrl_t *)arg;
    struct pbuf *q = p;

    if (err != ERR_OK) return err;
    if (p == NULL) {
        ctrl->pcb = NULL;
        return ERR_OK;
    }

    while (q != NULL) {
        uint8_t *data = (uint8_t *)q->payload;
        uint16_t n = q->len;
        uint16_t i = 0;
        while (i < n) {
            if (ctrl->rx_phase == CTRL_WAIT_STATE) {
                uint8_t st = data[i++];
                ctrl->server_state = st;
                sddf_printf("[iperf3] server state byte = %u (0x%02x)\n", st, st);

                if (st == PARAM_EXCHANGE) {
                    /* Build the param-exchange JSON from the runtime test
                     * parameters supplied by the serial `start` command. The
                     * "%u000000" prints the bitrate in bits/sec (Mbps * 1e6). */
                    char *json = ctrl->param_json;
                    if (ctrl->is_udp) {
                        if (ctrl->target_bw_mbps) {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"udp\":true,\"time\":%u,\"parallel\":%u,\"len\":%u,\"bitrate\":%u000000}",
                                ctrl->duration_s, ctrl->num_streams, ctrl->payload_len,
                                ctrl->target_bw_mbps);
                        } else {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"udp\":true,\"time\":%u,\"parallel\":%u,\"len\":%u}",
                                ctrl->duration_s, ctrl->num_streams, ctrl->payload_len);
                        }
                    } else {
                        if (ctrl->target_bw_mbps) {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"tcp\":true,\"time\":%u,\"omit\":%u,\"parallel\":%u,\"bitrate\":%u000000}",
                                ctrl->duration_s, ctrl->omit_s, ctrl->num_streams,
                                ctrl->target_bw_mbps);
                        } else {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"tcp\":true,\"time\":%u,\"omit\":%u,\"parallel\":%u}",
                                ctrl->duration_s, ctrl->omit_s, ctrl->num_streams);
                        }
                    }
                    ctrl->duration_ms = ctrl->duration_s * 1000;
                    ctrl->omit_ms = ctrl->omit_s * 1000;
                    uint32_t json_length = strlen(json);
                    uint32_t be = htonl(json_length);
                    memcpy(ctrl->json_len_buf, &be, 4);
                    ctrl->tx_buf = (const int8_t *)ctrl->json_len_buf;
                    ctrl->tx_len = 4;
                    ctrl->tx_off = 0;
                    iperf3_ctrl_maybe_tx(ctrl);
                    ctrl->tx_buf = (const int8_t *)json;
                    ctrl->tx_len = json_length;
                    ctrl->tx_off = 0;
                    iperf3_ctrl_maybe_tx(ctrl);

                } else if (st == CREATE_STREAMS) {
                    /* ctrl->num_streams was set by the serial `start` command. */
                  if (ctrl->is_udp) {
                    for (int s = 0; s < ctrl->num_streams; s++) {
                        iperf3_udp_stream_t *udp_stream = &ctrl->udp_streams[s];
                        udp_stream->pcb = udp_new();
                        sddf_printf("udp_new stream=%d pcb=%p\n", s, udp_stream->pcb);
                        if (udp_stream->pcb == NULL) {
                            sddf_printf("Failed to create UDP PCB for stream %d\n", s);
                            continue;
                        }
                        udp_bind(udp_stream->pcb, IP4_ADDR_ANY, 5210 + s);
                        udp_recv(udp_stream->pcb, udp_stream_recv, udp_stream);
                        udp_stream->server_addr = tpcb->remote_ip;
                        udp_stream->server_port = ctrl->server_port ? ctrl->server_port : 5202;
                        udp_stream->bytes_sent = 0;
                        udp_stream->seq_num = 0;
                        udp_stream->ctrl = ctrl;
                        udp_stream->phase = MESSAGE_SEND;

                        struct pbuf *pb = pbuf_alloc(PBUF_TRANSPORT, sizeof(uint32_t), PBUF_RAM);
                        if (!pb) {
                            sddf_printf("pbuf alloc failed\n");
                            continue;
                        }
                        uint32_t msg = htonl(UDP_CONNECT_MSG);
                        memcpy(pb->payload, &msg, sizeof(msg));
                        err_t serr = udp_sendto(udp_stream->pcb, pb, &udp_stream->server_addr, udp_stream->server_port);
                        sddf_printf("udp cookie send stream=%d err=%d\n", s, serr);
                        pbuf_free(pb);
                    }
                  } else {
                    for (int s = 0; s < ctrl->num_streams; s++) {
                        struct tcp_pcb *stream_pcb = tcp_new_ip_type(IPADDR_TYPE_V4);
                        if (stream_pcb == NULL) {
                            sddf_printf("iperf3_ctrl_recv: failed to create stream PCB\n");
                            continue;
                        }
                        err_t error = tcp_bind(stream_pcb, IP_ANY_TYPE, 0);
                        if (error) {
                            sddf_printf("Failed to bind TCP socket for stream: %s\n", lwip_strerr(error));
                            tcp_abort(stream_pcb);
                            continue;
                        }
                        iperf3_stream_t *stream = &ctrl->streams[s];
                        iperf3_stream_init(stream, ctrl->cookie, ctrl);
                        stream->pcb = stream_pcb;
                        tcp_arg(stream_pcb, stream);
                        error = tcp_connect(stream_pcb, &tpcb->remote_ip,
                                            ctrl->server_port ? ctrl->server_port : 5202,
                                            iperf3_stream_connect);
                        if (error) {
                            sddf_printf("Failed to connect TCP stream: %s\n", lwip_strerr(error));
                            tcp_abort(stream_pcb);
                            continue;
                        }
                    }
                  }

                } else if (st == TEST_START) {
                    ctrl->omit_end_ms = (sddf_timer_time_now(timer_config.driver_id) / 1000000) + ctrl->omit_ms;
                    ctrl->end_time_ms = ctrl->omit_end_ms + ctrl->duration_ms;
                    ctrl->test_active = true;
                    ctrl->omitting = true;
                    for (int k = 0; k < PAYLOAD_SIZE; k++) {
                        ctrl->payload[k] = (uint8_t)(k & 0xFF);
                    }
                  if (ctrl->is_udp) {
                    for (int s = 0; s < MAX_STREAMS; s++) {
                        iperf3_udp_stream_t *stream = &ctrl->udp_streams[s];
                        if (stream->pcb == NULL) continue;
                        stream->phase = SEND_PAYLOAD;
                        /* Datagrams per 100ms tick to hit the rate target; the
                         * pump is driven 10x/sec (LWIP_TICK_MS). 0 = unlimited. */
                        if (ctrl->target_bw_mbps) {
                            stream->burst_max = ((uint64_t)ctrl->target_bw_mbps * 1000000UL)
                                                / (8UL * (uint64_t)ctrl->payload_len * 10UL);
                            if (stream->burst_max == 0) stream->burst_max = 1;
                        } else {
                            stream->burst_max = 10000;
                        }
                        stream->tx_buf = ctrl->payload;
                        stream->payload_len = ctrl->payload_len;
                        stream->ctrl = ctrl;
                    }
                  } else {
                    for (int s = 0; s < MAX_STREAMS; s++) {
                        iperf3_stream_t *stream = &ctrl->streams[s];
                        if (stream->pcb == NULL) break;
                        stream->phase = SEND_PAYLOAD;
                        stream->tx_buf = ctrl->payload;
                        stream->tx_len = PAYLOAD_SIZE;
                        stream->tx_off = 0;
                        stream->ctrl = ctrl;
                        stream->bytes_this_tick = 0;
                        /* Bytes per 100ms tick to hit the rate target. 0 = unlimited. */
                        stream->tick_byte_limit = ctrl->target_bw_mbps
                            ? (uint32_t)(((uint64_t)ctrl->target_bw_mbps * 1000000UL) / (8UL * 10UL))
                            : 0;
                        iperf3_stream_maybe_tx(stream);
                    }
                  }

                } else if (st == TEST_RUNNING) {
                    /* nothing */

                } else if (st == EXCHANGE_RESULTS) {
                    ctrl->rx_phase = CTRL_WAIT_JSON_LEN;
                  if (ctrl->is_udp) {
                    /* UDP: send stub results JSON */
                    const char *json =
                        "{\"cpu_util_total\":0.00,\"cpu_util_user\":0.00,"
                        "\"cpu_util_system\":0.00,\"sender_has_retransmits\":0,"
                        "\"congestion_used\":\"cubic\","
                        "\"streams\":[{\"id\":1,\"bytes\":0,\"retransmits\":0,"
                        "\"jitter\":0.0,\"errors\":0,\"omitted_errors\":0,"
                        "\"packets\":0,\"omitted_packets\":0,"
                        "\"start_time\":0.0,\"end_time\":5.0}],"
                        "\"server_output_text\":\"\"}";
                    uint32_t json_length = strlen(json);
                    uint32_t be = htonl(json_length);
                    memcpy(ctrl->json_len_buf, &be, 4);
                    ctrl->tx_buf = (const int8_t *)ctrl->json_len_buf;
                    ctrl->tx_len = 4;
                    ctrl->tx_off = 0;
                    iperf3_ctrl_maybe_tx(ctrl);
                    ctrl->tx_buf = (const int8_t *)json;
                    ctrl->tx_len = json_length;
                    ctrl->tx_off = 0;
                    iperf3_ctrl_maybe_tx(ctrl);
                  } else {
                    uint64_t total_bytes = 0;
                    for (int s = 0; s < ctrl->num_streams; s++) {
                        total_bytes += ctrl->streams[s].bytes;
                    }
                    /* RTT already printed before MQ_EXIT (iperf3_client.c); re-aggregate
                     * here only to populate the results JSON for the server. */
                    uint32_t rmin, rmean, rmax, rsd; uint64_t rcnt;
                    iperf3_tcp_rtt_aggregate(ctrl, &rmin, &rmean, &rmax, &rsd, &rcnt);
                    (void)rsd; (void)rcnt;
                    sddf_snprintf(ctrl->json_send_buf, sizeof(ctrl->json_send_buf),
                        "{\"cpu_util_total\":%.2f,\"cpu_util_user\":%.2f,"
                        "\"cpu_util_system\":0.00,\"sender_has_retransmits\":0,"
                        "\"congestion_used\":\"cubic\","
                        "\"streams\":[{\"id\":1,\"bytes\":%llu,\"retransmits\":0,"
                        "\"min_rtt\":%u,\"max_rtt\":%u,\"mean_rtt\":%u,"
                        "\"jitter\":0.0,\"errors\":0,\"omitted_errors\":0,"
                        "\"packets\":0,\"omitted_packets\":0,"
                        "\"start_time\":0.0,\"end_time\":10.0}],"
                        "\"server_output_text\":\"\"}",
                        ctrl->cpu_util_percent, ctrl->cpu_util_percent,
                        (unsigned long long)total_bytes, rmin, rmax, rmean);
                    uint32_t json_length = strlen(ctrl->json_send_buf);
                    uint32_t be = htonl(json_length);
                    memcpy(ctrl->json_len_buf, &be, 4);
                    ctrl->tx_buf = (const int8_t *)ctrl->json_len_buf;
                    ctrl->tx_len = 4;
                    ctrl->tx_off = 0;
                    iperf3_ctrl_maybe_tx(ctrl);
                    ctrl->tx_buf = (const int8_t *)ctrl->json_send_buf;
                    ctrl->tx_len = json_length;
                    ctrl->tx_off = 0;
                    iperf3_ctrl_maybe_tx(ctrl);
                  }
                } else if (st == DISPLAY_RESULTS) {
                    sddf_printf("[iperf3] BENCHMARK_COMPLETE\n");
                    iperf_set_send_state(ctrl, IPERF_DONE);
                }

            } else if (ctrl->rx_phase == CTRL_WAIT_JSON_LEN) {
                while (i < n && ctrl->json_len_rx < 4) {
                    ctrl->json_len_buf[ctrl->json_len_rx++] = data[i++];
                }
                if (ctrl->json_len_rx == 4) {
                    ctrl->json_len = read_be32(ctrl->json_len_buf);
                    ctrl->json_rx = 0;
                    ctrl->json_len_rx = 0;
                    ctrl->rx_phase = CTRL_WAIT_JSON_BODY;
                }
            } else if (ctrl->rx_phase == CTRL_WAIT_JSON_BODY) {
                uint32_t to_copy = ctrl->json_len - ctrl->json_rx > n - i
                                   ? n - i : ctrl->json_len - ctrl->json_rx;
                memcpy(ctrl->result_json + ctrl->json_rx, data + i, to_copy);
                ctrl->json_rx += to_copy;
                i += to_copy;
                if (ctrl->json_rx == ctrl->json_len) {
                    ctrl->result_json[ctrl->json_rx] = '\0';
                    sddf_printf("\n[iperf3] ===== Received server results JSON (%u bytes) =====\n%s\n"
                                "[iperf3] ================================================\n",
                                ctrl->json_len, ctrl->result_json);
                    ctrl->rx_phase = CTRL_WAIT_STATE;
                    ctrl->json_rx = 0;
                }
            }
        }
        q = q->next;
    }
    tcp_recved(tpcb, p->tot_len);
    pbuf_free(p);
    return ERR_OK;
}

err_t iperf_ctrl_sent(void *arg, struct tcp_pcb *tpcb, u16_t len) {
    iperf_ctrl_t *ctrl = (iperf_ctrl_t *)arg;
    (void)tpcb;
    (void)len;
    iperf3_ctrl_maybe_tx(ctrl);
    return ERR_OK;
}

void iperf3_ctrl_err(void *arg, err_t err) {
    iperf_ctrl_t *ctrl = (iperf_ctrl_t *)arg;
    (void)err;
    ctrl->pcb = NULL;
}

static void iperf_timer_tick(iperf_ctrl_t *ctrl, uint32_t now_ms) {
    if (ctrl->test_active && !ctrl->test_done && now_ms >= ctrl->end_time_ms)
        ctrl->test_done = true;
    if (ctrl->test_active && ctrl->omitting && now_ms >= ctrl->omit_end_ms)
        ctrl->omitting = false;
}

/* UDP data path: pump datagrams each tick and, past the deadline, tear down the
 * UDP streams and send TEST_END. Called (for UDP tests only) from the timer /
 * net_tx branches in iperf3_client.c notified(). */
void iperf3_on_timer_tick(iperf_ctrl_t *ctrl, uint32_t now_ms) {
    iperf_timer_tick(ctrl, now_ms);

    if (ctrl->test_active && !ctrl->test_done) {
        for (int s = 0; s < ctrl->num_streams; s++) {
            iperf3_udp_stream_t *stream = &ctrl->udp_streams[s];
            if (stream->pcb != NULL && stream->phase == SEND_PAYLOAD) {
                stream->tx_buf = ctrl->payload;
                stream->payload_len = ctrl->payload_len;
                stream->ctrl = ctrl;
                udp_pump(stream);
            }
        }
    }

    if (ctrl->test_active && ctrl->test_done && !ctrl->sent_test_end) {
        for (int s = 0; s < ctrl->num_streams; s++) {
            if (ctrl->udp_streams[s].pcb) {
                udp_remove(ctrl->udp_streams[s].pcb);
                ctrl->udp_streams[s].pcb = NULL;
            }
        }
        ctrl->sent_test_end = true;
        iperf_set_send_state(ctrl, TEST_END);
    }
}

/* TCP data path: evaluate the test-duration deadline and, once past it, stop the
 * streams and send TEST_END. Called both from lwIP's poll callback (when the
 * timer works, e.g. single-core) and from the data path in notified() (the only
 * thing that runs on a client placed on a non-timer core — see iperf3_client.c).
 * No-op for UDP tests (their termination is in iperf3_on_timer_tick). */
void iperf3_tcp_check_deadline(iperf_ctrl_t *ctrl, uint32_t now_ms) {
    if (ctrl->is_udp) return;
    iperf_timer_tick(ctrl, now_ms);
    if (ctrl->test_done && !ctrl->sent_test_end) {
        for (int i = 0; i < MAX_STREAMS; i++) {
            ctrl->bytes_sent += ctrl->streams[i].bytes;
            ctrl->streams[i].phase = STOPPED;
        }
        ctrl->sent_test_end = true;
        iperf_set_send_state(ctrl, TEST_END);
    }
}

static err_t iperf_poll(void *arg, struct tcp_pcb *tpcb) {
    iperf_ctrl_t *ctrl = (iperf_ctrl_t *)arg;
    (void)tpcb;
    uint32_t now = sddf_timer_time_now(timer_config.driver_id) / 1000000;
    iperf3_tcp_check_deadline(ctrl, now);
    return ERR_OK;
}

err_t iperf_ctrl_connect(void *arg, struct tcp_pcb *pcb, err_t err) {
    iperf_ctrl_t *ctrl = arg;
    if (err != ERR_OK) return err;
    if (pcb == NULL) return ERR_MEM;

    ctrl->pcb = pcb;
    tcp_arg(pcb, ctrl);
    tcp_recv(pcb, iperf_ctrl_recv);
    tcp_sent(pcb, iperf_ctrl_sent);
    tcp_err(pcb, iperf3_ctrl_err);
    /* Drives the TCP deadline check; iperf3_tcp_check_deadline no-ops for UDP. */
    tcp_poll(pcb, iperf_poll, 1);

    ctrl->tx_buf = (const int8_t *)ctrl->cookie;
    ctrl->tx_len = IPERF3_COOKIE_LEN;
    ctrl->tx_off = 0;
    iperf3_ctrl_maybe_tx(ctrl);
    ctrl->rx_phase = CTRL_WAIT_STATE;
    return ERR_OK;
}
