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
#include "mjson.h"

#include "iperf3_ctrl.h"
#include "mjson.h"

#define IPERF_START 15
#define PARAM_EXCHANGE   9
#define CREATE_STREAMS  10
#define TEST_START       1
#define TEST_RUNNING     2
#define TEST_END         4
#define EXCHANGE_RESULTS 13
#define DISPLAY_RESULTS  14
#define IPERF_DONE       16

#define COOKIE_LEN 37

#define UDP_CONNECT_MSG 0x36373839

extern timer_client_config_t timer_config;

static uint32_t read_be32(const uint8_t b[4]) {
    return ((uint32_t)b[0] << 24) |
           ((uint32_t)b[1] << 16) |
           ((uint32_t)b[2] <<  8) |
           ((uint32_t)b[3] <<  0);
}

/* Integer sqrt for RTT stddev */
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

/* parse json into ctrl arguments*/
void parse_test_params(const char *json, iperf_ctrl_t *ctrl) {
    int len = (int)strlen(json);
    double d;
    int b;

    ctrl->is_udp = (mjson_get_bool(json, len, "$.udp", &b) && b);

    if (mjson_get_number(json, len, "$.time", &d)) {
        ctrl->duration_s  = (uint32_t)d;
        ctrl->duration_ms = ctrl->duration_s * 1000;
    }

    if (mjson_get_number(json, len, "$.omit", &d)) {
        ctrl->omit_s  = (uint32_t)d;
        ctrl->omit_ms = ctrl->omit_s * 1000;
    }

    if (mjson_get_number(json, len, "$.parallel", &d)) {
        ctrl->num_streams = (uint8_t)d;
    }

    if (mjson_get_number(json, len, "$.len", &d)) {
        ctrl->payload_len = (uint16_t)d;
    }

    if (mjson_get_number(json, len, "$.bitrate", &d)) {
        ctrl->target_bw_mbps = (uint32_t)(d / 1000000.0);
    }

    ctrl->is_reverse       = (mjson_get_bool(json, len, "$.reverse", &b) && b);
    ctrl->is_bidirectional = (mjson_get_bool(json, len, "$.bidirectional", &b) && b);
}

/* listen on server */
void iperf3_server_listen(iperf_ctrl_t *ctrl, uint32_t port) {

    iperf3_ctrl_init(ctrl);
    ctrl->role = 's';

    struct tcp_pcb *pcb = tcp_new_ip_type(IPADDR_TYPE_ANY);
    if (pcb == NULL) {
        sddf_printf("iperf3_server_listen: failed to create PCB\n");
        return;
    }

    err_t err = tcp_bind(pcb, IP_ANY_TYPE, (uint16_t)port);
    if (err != ERR_OK) {
        sddf_printf("iperf3_server_listen: bind failed: %s\n", lwip_strerr(err));
        tcp_abort(pcb);
        return;
    }
    struct tcp_pcb *lpcb = tcp_listen(pcb);
    if (lpcb == NULL) {
        sddf_printf("iperf3_server_listen: listen failed\n");
        tcp_abort(pcb);
        return;
    }
    ctrl->prot_listen = lpcb;

    tcp_arg(lpcb, ctrl);
    tcp_accept(lpcb, iperf3_server_accept_ctrl);
    sddf_printf("[iperf3] server listening on port %u\n", (unsigned)port);
}

/* server accept client ctrl */
err_t iperf3_server_accept_ctrl(void* arg, struct tcp_pcb *new_pcb, err_t err) {
    iperf_ctrl_t *ctrl = (iperf_ctrl_t *)arg;
    sddf_printf("[iperf3] accept fired: err=%d state=%u set=%d\n",
                (int)err, ctrl ? ctrl->server_state : 999, ctrl ? ctrl->set : 999);
    if (err != ERR_OK || new_pcb == NULL) return ERR_VAL;

    /* Control connection has set == -1 */
    if (ctrl->server_state != CREATE_STREAMS && ctrl->set == -1) {
        ctrl->pcb = new_pcb;
        ctrl->set = 0;
        tcp_arg(new_pcb, ctrl);
        tcp_recv(new_pcb, iperf_ctrl_recv_server);
        tcp_sent(new_pcb, iperf_ctrl_sent);
        tcp_err(new_pcb, iperf3_ctrl_err);

        ctrl->server_state = IPERF_START;
        ctrl->cookie_recv = 0;
        ctrl->rx_phase = CTRL_WAIT_STATE;

    } else if (ctrl->server_state == CREATE_STREAMS) {
        if (ctrl->is_udp) {
            /* TCP forward only support atm */
        } else {
            int idx = -1;
            for (int s = 0; s < MAX_STREAMS; s++) {
                if (ctrl->streams[s].pcb == NULL) { idx = s; break; }
            }
            if (idx < 0) {
                tcp_abort(new_pcb);
                return ERR_ABRT;
            }
            iperf3_stream_t *stream = &ctrl->streams[idx];
            stream->pcb = new_pcb;
            stream->cookie_rx_len = 0;
            stream->bytes = 0;
            stream->rx_bytes = 0;
            stream->is_sender = false;
            stream->phase = STOPPED;
            stream->ctrl = ctrl;
            tcp_arg(new_pcb, stream);
            tcp_recv(new_pcb, iperf3_server_stream_recv);
            tcp_err(new_pcb, iperf3_stream_err);
        }
    }
    return ERR_OK;
}

/* Aggregate RTT (us) across all TCP streams */
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
    ctrl->cookie_recv = 0;
    ctrl->server_state = 0;
    ctrl->json_len = 0;
    ctrl->json_rx = 0;
    ctrl->json_len_rx = 0;
    ctrl->sent_test_end = false;
    ctrl->test_active = false;
    ctrl->test_done = false;
    ctrl->bytes_sent = 0;
    ctrl->omitting = false;
    ctrl->num_streams = 1;
    ctrl->target_bw_mbps = 0;
    ctrl->payload_len = 1460;
    ctrl->is_udp = false;
    ctrl->duration_s = 10;
    ctrl->omit_s = 5;
    ctrl->role = 'c';
    ctrl->set = -1;
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

/* Called from the data-stream recv once a stream's cookie is fully received */
void iperf3_server_stream_ready(iperf_ctrl_t *ctrl) {
    ctrl->rec_streams_accepted++;
    sddf_printf("[iperf3] stream ready %u/%u\n",
                ctrl->rec_streams_accepted, ctrl->num_streams);
    if (ctrl->rec_streams_accepted == ctrl->num_streams) {
        sddf_printf("[iperf3] all streams ready -> TEST_START/TEST_RUNNING\n");
        iperf_set_send_state(ctrl, TEST_START);
        iperf_set_send_state(ctrl, TEST_RUNNING);
        ctrl->test_active = true;
    }
}

// add a read length function
err_t iperf_ctrl_recv_server(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err) {
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
            if (ctrl->server_state == IPERF_START) {
                ctrl->cookie[ctrl->cookie_recv] = data[i];
                ctrl->cookie_recv++;
                i++;
                if (ctrl->cookie_recv == IPERF3_COOKIE_LEN) {
                    /* ask the client for its parameters */
                    sddf_printf("[iperf3] cookie received -> sending PARAM_EXCHANGE\n");
                    ctrl->rx_phase = CTRL_WAIT_JSON_LEN;
                    iperf_set_send_state(ctrl, PARAM_EXCHANGE);
                }
            } else if (ctrl->server_state == PARAM_EXCHANGE) {
                if (ctrl->rx_phase == CTRL_WAIT_JSON_LEN) {
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
                
                    memcpy(ctrl->param_json + ctrl->json_rx, data + i, to_copy);
                    ctrl->json_rx += to_copy;
                    i += to_copy;
                    if (ctrl->json_rx == ctrl->json_len) {
                        ctrl->param_json[ctrl->json_rx] = '\0';
                        ctrl->rx_phase = CTRL_WAIT_STATE;
                        ctrl->json_rx = 0;

                        /* Parse params then tell client to create streams */
                        parse_test_params(ctrl->param_json, ctrl);
                        sddf_printf("[iperf3] params: json=%s\n", ctrl->param_json);
                        sddf_printf("[iperf3] parsed udp=%d streams=%u dur=%u -> CREATE_STREAMS\n",
                                    ctrl->is_udp, ctrl->num_streams, ctrl->duration_s);
                        ctrl->send_streams_accepted = 0;
                        ctrl->rec_streams_accepted = 0;
                        iperf_set_send_state(ctrl, CREATE_STREAMS);
                    }
                } else {
                    i++;
                }
            } else if (ctrl->server_state == TEST_RUNNING) {
                uint8_t st = data[i++];
                if (st == TEST_END) {
                    iperf_set_send_state(ctrl, EXCHANGE_RESULTS);
                }
            } else if (ctrl->server_state == EXCHANGE_RESULTS) {
                if (ctrl->rx_phase == CTRL_WAIT_JSON_LEN) {
                    // receive the results
                    ctrl->json_len_buf[ctrl->json_len_rx++] = data[i++];
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
                        sddf_printf("\n[iperf3] ===== Received client results JSON (%u bytes) =====\n%s\n"
                                    "[iperf3] ================================================\n",
                                    ctrl->json_len, ctrl->result_json);
                        ctrl->rx_phase = CTRL_WAIT_STATE;
                        ctrl->json_rx = 0;
                    }
                }
                
                // create results and send them

                // send iperf_done
            }
        }
        q = q->next;
    }
    tcp_recved(tpcb, p->tot_len);
    pbuf_free(p);
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

                    char *json = ctrl->param_json;

                    const char *rev = ctrl->is_reverse ? ",\"reverse\":true" : "";
                    if (ctrl->is_udp) {
                        if (ctrl->target_bw_mbps) {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"udp\":true,\"time\":%u,\"parallel\":%u,\"len\":%u,\"bitrate\":%u000000%s}",
                                ctrl->duration_s, ctrl->num_streams, ctrl->payload_len,
                                ctrl->target_bw_mbps, rev);
                        } else {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"udp\":true,\"time\":%u,\"parallel\":%u,\"len\":%u%s}",
                                ctrl->duration_s, ctrl->num_streams, ctrl->payload_len, rev);
                        }
                    } else {
                        if (ctrl->target_bw_mbps) {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"tcp\":true,\"time\":%u,\"omit\":%u,\"parallel\":%u,\"bitrate\":%u000000%s}",
                                ctrl->duration_s, ctrl->omit_s, ctrl->num_streams,
                                ctrl->target_bw_mbps, rev);
                        } else {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"tcp\":true,\"time\":%u,\"omit\":%u,\"parallel\":%u%s}",
                                ctrl->duration_s, ctrl->omit_s, ctrl->num_streams, rev);
                        }
                    }

                    const char *bi = ctrl->is_bidirectional ? ",\"bidirectional\":true" : "";
                    if (ctrl->is_udp) {
                        if (ctrl->target_bw_mbps) {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"udp\":true,\"time\":%u,\"parallel\":%u,\"len\":%u,\"bitrate\":%u000000%s}",
                                ctrl->duration_s, ctrl->num_streams, ctrl->payload_len,
                                ctrl->target_bw_mbps, bi);
                        } else {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"udp\":true,\"time\":%u,\"parallel\":%u,\"len\":%u%s}",
                                ctrl->duration_s, ctrl->num_streams, ctrl->payload_len, bi);
                        }
                    } else {
                        if (ctrl->target_bw_mbps) {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"tcp\":true,\"time\":%u,\"omit\":%u,\"parallel\":%u,\"bitrate\":%u000000%s}",
                                ctrl->duration_s, ctrl->omit_s, ctrl->num_streams,
                                ctrl->target_bw_mbps, bi);
                        } else {
                            sddf_snprintf(json, sizeof(ctrl->param_json),
                                "{\"tcp\":true,\"time\":%u,\"omit\":%u,\"parallel\":%u%s}",
                                ctrl->duration_s, ctrl->omit_s, ctrl->num_streams, bi);
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
                    for (int s = 0; s < (ctrl->is_bidirectional + 1) * ctrl->num_streams; s++) {
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
                        udp_stream->rx_bytes = 0;
                        udp_stream->rx_packets = 0;
                        udp_stream->rx_first_seq = 0;
                        udp_stream->rx_last_seq = 0;
                        udp_stream->rx_have_first = 0;
                        udp_stream->rx_jitter = 0.0;
                        udp_stream->rx_prev_transit = 0.0;
                        udp_stream->is_sender = true;

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
                    for (int s = 0; s < (ctrl->is_bidirectional + 1) * ctrl->num_streams; s++) {
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
                  if (ctrl->is_reverse) {
                    for (int s = 0; s < MAX_STREAMS; s++) {
                        ctrl->streams[s].phase = STOPPED;
                        ctrl->udp_streams[s].phase = STOPPED;
                        ctrl->streams[s].is_sender = false;
                        ctrl->udp_streams[s].is_sender = false;
                    }

                  } else if (ctrl->is_bidirectional) {
                    int req_streams = ctrl->num_streams;
                        for (int k = 0; k < PAYLOAD_SIZE; k++) {
                            ctrl->payload[k] = (uint8_t)(k & 0xFF);
                        }
                    if (ctrl->is_udp) {
                        for (int s = 0; s < req_streams; s++) {
                            iperf3_udp_stream_t *stream = &ctrl->udp_streams[s];
                            if (stream->pcb == NULL) continue;
                            stream->phase = SEND_PAYLOAD;
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
                            stream->is_sender = true;
                        }
                        for (int s = req_streams; s < 2 * req_streams; s++) {
                            ctrl->streams[s].phase = STOPPED;
                            ctrl->udp_streams[s].phase = STOPPED;
                            ctrl->streams[s].is_sender = false;
                            ctrl->udp_streams[s].is_sender = false;
                        }
                    } else {
                        for (int s = 0; s < req_streams; s++) {
                            iperf3_stream_t *stream = &ctrl->streams[s];
                            if (stream->pcb == NULL) break;
                            stream->phase = SEND_PAYLOAD;
                            stream->tx_buf = ctrl->payload;
                            stream->tx_len = PAYLOAD_SIZE;
                            stream->tx_off = 0;
                            stream->ctrl = ctrl;
                            stream->is_sender = true;
                            stream->bytes_this_tick = 0;
                            stream->tick_byte_limit = ctrl->target_bw_mbps
                                ? (uint32_t)(((uint64_t)ctrl->target_bw_mbps * 1000000UL) / (8UL * 10UL))
                                : 0;
                            iperf3_stream_maybe_tx(stream);
                        }
                        for (int s = req_streams; s < 2 * req_streams; s++) {
                            ctrl->streams[s].phase = STOPPED;
                            ctrl->udp_streams[s].phase = STOPPED;
                            ctrl->streams[s].is_sender = false;
                            ctrl->udp_streams[s].is_sender = false;
                        }
                    }
                  } else {
                        for (int k = 0; k < PAYLOAD_SIZE; k++) {
                            ctrl->payload[k] = (uint8_t)(k & 0xFF);
                        }
                    if (ctrl->is_udp) {
                        for (int s = 0; s < MAX_STREAMS; s++) {
                            iperf3_udp_stream_t *stream = &ctrl->udp_streams[s];
                            if (stream->pcb == NULL) continue;
                            stream->phase = SEND_PAYLOAD;

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
                            stream->is_sender = true;
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
                            stream->is_sender = true;
                            stream->bytes_this_tick = 0;
                            /* Bytes per 100ms tick to hit the rate target. 0 = unlimited. */
                            stream->tick_byte_limit = ctrl->target_bw_mbps
                                ? (uint32_t)(((uint64_t)ctrl->target_bw_mbps * 1000000UL) / (8UL * 10UL))
                                : 0;
                            iperf3_stream_maybe_tx(stream);
                        }
                    }
                  }

                } else if (st == TEST_RUNNING) {
                    /* nothing data flows via the stream callbacks */

                } else if (st == EXCHANGE_RESULTS) {
                    ctrl->rx_phase = CTRL_WAIT_JSON_LEN;
                  if (ctrl->is_udp) {
                    char *buf = ctrl->json_send_buf;
                    size_t cap = sizeof(ctrl->json_send_buf);
                    int off = 0;
                    off += sddf_snprintf(buf + off, cap - off,
                        "{\"cpu_util_total\":%.2f,\"cpu_util_user\":%.2f,"
                        "\"cpu_util_system\":0.00,\"sender_has_retransmits\":0,"
                        "\"congestion_used\":\"cubic\",\"streams\":[",
                        ctrl->cpu_util_percent, ctrl->cpu_util_percent);
                    /* (id 1, then 3,4,5..)
                     * UDP senders report the
                     * datagrams/bytes they pumped; receivers report what arrived plus
                     * loss (from the sender-seq span) and RFC1889 jitter. */
                    uint32_t total = (uint32_t)(ctrl->is_bidirectional + 1) * ctrl->num_streams;
                    for (uint32_t s = 0; s < total; s++) {
                        iperf3_udp_stream_t *us = &ctrl->udp_streams[s];
                        int id = (s == 0) ? 1 : (int)(2 + s);
                        uint64_t bytes, packets;
                        int lost = 0;
                        double jitter = 0.0;
                        if (us->is_sender) {
                            bytes = us->bytes_sent;
                            packets = us->packets_sent;
                        } else {
                            bytes = us->rx_bytes;
                            packets = us->rx_packets;
                            jitter = us->rx_jitter;
                            if (us->rx_have_first) {
                                int expected = (int)(us->rx_last_seq - us->rx_first_seq) + 1;
                                lost = expected - (int)us->rx_packets;
                                if (lost < 0) lost = 0;
                            }
                        }
                        off += sddf_snprintf(buf + off, cap - off,
                            "%s{\"id\":%d,\"bytes\":%llu,\"retransmits\":0,"
                            "\"jitter\":%.6f,\"errors\":%d,\"omitted_errors\":0,"
                            "\"packets\":%llu,\"omitted_packets\":0,"
                            "\"start_time\":0.0,\"end_time\":%u.0}",
                            s == 0 ? "" : ",", id,
                            (unsigned long long)bytes, jitter, lost,
                            (unsigned long long)packets, ctrl->duration_s);
                    }
                    off += sddf_snprintf(buf + off, cap - off,
                        "],\"server_output_text\":\"\"}");
                    sddf_printf("[results-tx] %s\n", ctrl->json_send_buf);
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
                  } else {
                    char *buf = ctrl->json_send_buf;
                    size_t cap = sizeof(ctrl->json_send_buf);
                    int off = 0;

                    off += sddf_snprintf(buf + off, cap - off,
                        "{\"cpu_util_total\":%.2f,\"cpu_util_user\":%.2f,"
                        "\"cpu_util_system\":0.00,\"sender_has_retransmits\":0,"
                        "\"congestion_used\":\"cubic\",\"streams\":[",
                        ctrl->cpu_util_percent, ctrl->cpu_util_percent);

                    uint32_t total = (uint32_t)(ctrl->is_bidirectional + 1) * ctrl->num_streams;
                    for (uint32_t s = 0; s < total; s++) {
                        iperf3_stream_t *st = &ctrl->streams[s];
                        int id = (s == 0) ? 1 : (int)(2 + s);
                        uint64_t sbytes = st->is_sender ? st->bytes : st->rx_bytes;
                        if (st->is_sender) {
                            uint32_t rmean = st->rtt_count ? (uint32_t)(st->rtt_sum_us / st->rtt_count) : 0;
                            off += sddf_snprintf(buf + off, cap - off,
                                "%s{\"id\":%d,\"bytes\":%llu,\"retransmits\":0,"
                                "\"min_rtt\":%u,\"max_rtt\":%u,\"mean_rtt\":%u,"
                                "\"jitter\":0.0,\"errors\":0,\"omitted_errors\":0,"
                                "\"packets\":0,\"omitted_packets\":0,"
                                "\"start_time\":0.0,\"end_time\":%u.0}",
                                s == 0 ? "" : ",", id,
                                (unsigned long long)sbytes,
                                st->rtt_count ? st->rtt_min_us : 0, st->rtt_max_us, rmean,
                                ctrl->duration_s);
                        } else {
                            off += sddf_snprintf(buf + off, cap - off,
                                "%s{\"id\":%d,\"bytes\":%llu,\"retransmits\":0,"
                                "\"jitter\":0.0,\"errors\":0,\"omitted_errors\":0,"
                                "\"packets\":0,\"omitted_packets\":0,"
                                "\"start_time\":0.0,\"end_time\":%u.0}",
                                s == 0 ? "" : ",", id,
                                (unsigned long long)sbytes,
                                ctrl->duration_s);
                        }
                    }
                    off += sddf_snprintf(buf + off, cap - off,
                        "],\"server_output_text\":\"\"}");
                    sddf_printf("[results-tx] %s\n", ctrl->json_send_buf);
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

/* UDP data path */
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

/* TCP data path */
void iperf3_tcp_check_deadline(iperf_ctrl_t *ctrl, uint32_t now_ms) {
    if (ctrl->is_udp || ctrl->role != 'c') return;
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
    tcp_poll(pcb, iperf_poll, 1);

    ctrl->tx_buf = (const int8_t *)ctrl->cookie;
    ctrl->tx_len = IPERF3_COOKIE_LEN;
    ctrl->tx_off = 0;
    iperf3_ctrl_maybe_tx(ctrl);
    ctrl->rx_phase = CTRL_WAIT_STATE;
    return ERR_OK;
}

err_t iperf_start_server(void *arg, struct tcp_pcb *pcb, err_t err) {
    iperf_ctrl_t *ctrl = arg;
    if (err != ERR_OK) return err;
    if (pcb == NULL) return ERR_MEM;

    ctrl->pcb = pcb;
    tcp_arg(pcb, ctrl);
    tcp_recv(pcb, iperf_ctrl_recv);
    tcp_sent(pcb, iperf_ctrl_sent);
    tcp_err(pcb, iperf3_ctrl_err);

    tcp_poll(pcb, iperf_poll, 1);

    ctrl->tx_buf = (const int8_t *)ctrl->cookie;
    ctrl->tx_len = IPERF3_COOKIE_LEN;
    ctrl->tx_off = 0;
    iperf3_ctrl_maybe_tx(ctrl);
    ctrl->rx_phase = CTRL_WAIT_STATE;
    return ERR_OK;
}