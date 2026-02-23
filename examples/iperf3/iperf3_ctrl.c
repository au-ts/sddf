
#include <stdint.h>
#include <stdbool.h>
#include "lwip/tcp.h"
#include "lwip/ip.h"
#include "lwip/pbuf.h"
#include "lwip/ip_addr.h"
#include <string.h>
#include <sddf/util/util.h>
#include <sddf/timer/config.h>
#include <sddf/timer/client.h>

#include "iperf3_ctrl.h"

#define PARAM_EXCHANGE  9
#define CREATE_STREAMS 10
#define TEST_START      1
#define TEST_RUNNING    2
#define TEST_END        4
#define EXCHANGE_RESULTS 13 
#define DISPLAY_RESULTS 14
#define IPERF_DONE 16

extern timer_client_config_t timer_config;

// Convert 4 byte big endian to uint32_t length
static uint32_t read_be32(const uint8_t b[4]) {
    return ((uint32_t)b[0] << 24) |
           ((uint32_t)b[1] << 16) |
           ((uint32_t)b[2] <<  8) |
           ((uint32_t)b[3] <<  0);
}

// initialise all ctrl state members
void iperf3_ctrl_init(iperf_ctrl_t *ctrl) {
    ctrl->pcb = NULL;
    memset(ctrl->cookie, 0, IPERF3_COOKIE_LEN);
    // starting phase is sending cookie to server then waiting for state byte back from server
    ctrl->rx_phase = CTRL_WAIT_STATE;
    ctrl->server_state = 0;
    ctrl->json_len = 0;
    ctrl->json_rx = 0;
    ctrl->json_len_rx = 0;
    ctrl->sent_test_end = false;
    ctrl->test_active = false;
    ctrl->test_done = false;
    ctrl->bytes_sent = 0;
    for (int i = 0; i < MAX_STREAMS; i++) {
      ctrl->streams[i].pcb = NULL;
      ctrl->streams[i].bytes = 0;
      ctrl->streams[i].phase = STOPPED;
    }
}

// maybe transmit data on the control connection
void iperf3_ctrl_maybe_tx(iperf_ctrl_t *ctrl) {
  if (ctrl->pcb == NULL) return;
  if (ctrl->tx_len == ctrl->tx_off) {
    return;
  }
  // ask how much space
  u16_t avail = tcp_sndbuf(ctrl->pcb);
  if (avail == 0) return;
  // compete chunk 
  u16_t remaining = ctrl->tx_len - ctrl->tx_off;
  u16_t chunk = remaining > avail ? avail : remaining;
  // try to enqueue
  err_t err = tcp_write(ctrl->pcb, ctrl->tx_buf + ctrl->tx_off, chunk, TCP_WRITE_FLAG_COPY);
  // if (err return
  if (err != ERR_OK) {
    return;
  }
  // advance progress
  ctrl->tx_off += chunk;
  // flush
  tcp_output(ctrl->pcb);
}

// sends the next state byte to the server
err_t iperf_set_send_state(iperf_ctrl_t *ctrl, signed int state) {
    ctrl->server_state = state;
    ctrl->tx_buf = (const int8_t *)&ctrl->server_state;
    ctrl->tx_len = 1;
    ctrl->tx_off = 0;
    iperf3_ctrl_maybe_tx(ctrl);
    return ERR_OK;
}

// when data arrives in the rx buffer receive the data and update ctrl state
err_t iperf_ctrl_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err) {
    iperf_ctrl_t *ctrl = (iperf_ctrl_t *)arg;
    struct pbuf *q = p;
    
    if (err != ERR_OK) {
      return err;
    }

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
          uint8_t st = data[i];
          ctrl->server_state = st;
          sddf_printf("[iperf3] server state byte = %u (0x%02x)\n",
                ctrl->server_state, ctrl->server_state); 
          i += 1;
          
          // test params are all hardcoded
          if (st == PARAM_EXCHANGE) {
            const char *json = "{\"tcp\":true,\"time\":5,\"parallel\":4}";

            // need to add omit, time, num(), blockcount(ehhh number of blocks), parallel len pacingtimer and client version
            ctrl->duration_ms = 5000;
            ctrl->omit_ms = 0000;
  
            // send the json length first as 4 byte big endian
            uint32_t json_length = strlen(json);
            uint32_t be = htonl(json_length);
            memcpy(ctrl->json_len_buf, &be, 4);
            ctrl->tx_buf = (const int8_t *)ctrl->json_len_buf;
            ctrl->tx_len = 4;
            ctrl->tx_off = 0;
            iperf3_ctrl_maybe_tx(ctrl);

            // then send the json body
            ctrl->tx_buf = (const int8_t *)json;
            ctrl->tx_len = json_length;
            ctrl->tx_off = 0;
            iperf3_ctrl_maybe_tx(ctrl);
          } else if (st == CREATE_STREAMS) {
            // start the number of streams agreed in params
            
            ctrl->num_streams = 4; // hardcoded for now

            // for each stream create tcp pcb and stream struct
            for (int s = 0; s < ctrl->num_streams; s++) {
                struct tcp_pcb *stream_pcb = tcp_new_ip_type(IPADDR_TYPE_V4);
                if (stream_pcb == NULL) {
                    sddf_printf("iperf3_ctrl_recv: failed to create stream PCB\n");
                    continue;
                }
                err_t error = tcp_bind(stream_pcb, IP_ANY_TYPE, 0);
                if (error) {
                    sddf_printf("Failed to bind TCP  socket for stream: %s\n", lwip_strerr(error));
                    tcp_abort(stream_pcb);
                    continue;
                }
                iperf3_stream_t *stream = &ctrl->streams[s];
                iperf3_stream_init(stream, ctrl->cookie, ctrl);
                stream->pcb = stream_pcb;

                tcp_arg(stream_pcb, stream);

                error = tcp_connect(stream_pcb, &tpcb->remote_ip, 5202, iperf3_stream_connect);
                if (error) {
                    sddf_printf("Failed to connect to TCP  socket for stream: %s\n", lwip_strerr(error));
                    tcp_abort(stream_pcb);
                    continue;
                }
            }
            // for each stream send cookie to server

            // then wait for server to send START_TEST state

          } else if (st == TEST_START) {
            
            // start test now
            ctrl->omit_end_ms = (sddf_timer_time_now(timer_config.driver_id) / 1000000) + ctrl->omit_ms;
            ctrl->end_time_ms = ctrl->omit_end_ms + ctrl->duration_ms; // 5 seconds from now
            ctrl->test_active = true;
            ctrl->omitting = true;
            // ctrl->rx_phase = TEST_RUNNING;
            for (int i = 0; i < PAYLOAD_SIZE; i++) {
                ctrl->payload[i] = (uint8_t)(i & 0xFF);
            }
            
            for (int s = 0; s < MAX_STREAMS; s++) {
                iperf3_stream_t *stream = &ctrl->streams[s];
                if (stream->pcb != NULL) {
                    // set stream to send payload now
                    stream->phase = SEND_PAYLOAD;
                    stream->tx_buf = ctrl->payload; // set to payload buffer
                    stream->tx_len = PAYLOAD_SIZE; // set to payload length
                    stream->tx_off = 0;
                    stream->ctrl = ctrl; // set back reference to ctrl
                    iperf3_stream_maybe_tx(stream);
                } else {
                  break;
                }
            }
           
          } else if (st == TEST_RUNNING) {
            // test is running
            
            // do nothing
          } else if (st == EXCHANGE_RESULTS) {
            ctrl->rx_phase = CTRL_WAIT_JSON_LEN;
            for (int s = 0; s < ctrl->num_streams; s++) {
              iperf3_stream_t *stream = &ctrl->streams[s];
            }

            // sddf_printf("[iperf3] Test complete, total bytes transferred: %llu\n", ctrl->bytes_sent);

            // Stub result so server can send results and state byte
            const char *json =
              "{\n"
              "  \"cpu_util_total\": 0.67,\n"
              "  \"cpu_util_user\": 0.45,\n"
              "  \"cpu_util_system\": 0.22,\n"
              "  \"sender_has_retransmits\": 0,\n"
              "  \"congestion_used\": \"cubic\",\n"
              "  \"streams\": [\n"
              "    {\n"
              "      \"id\": 1,\n"
              "      \"bytes\": 12345678,\n"
              "      \"retransmits\": 0,\n"
              "      \"jitter\": 0.0001,\n"
              "      \"errors\": 0,\n"
              "      \"omitted_errors\": 0,\n"
              "      \"packets\": 1500,\n"
              "      \"omitted_packets\": 0,\n"
              "      \"start_time\": 0.000000,\n"
              "      \"end_time\": 10.000000\n"
              "    }\n"
              "  ],\n"
              "  \"server_output_text\": \"\"\n"
              "}";

            ctrl->tx_buf = (const int8_t *)json;
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
          } else if (st == DISPLAY_RESULTS) {
            iperf_set_send_state(ctrl, IPERF_DONE);
          }
        } else if (ctrl->rx_phase == CTRL_WAIT_JSON_LEN) {
                      sddf_printf("[iperf3] server state byte = %u (0x%02x)\n",
                ctrl->server_state, ctrl->server_state);
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
          uint32_t to_copy = ctrl->json_len - ctrl->json_rx > n - i ? n - i : ctrl->json_len - ctrl->json_rx;
          // process json data in data + i, length to_copy
          memcpy(ctrl->result_json + ctrl->json_rx, data + i, to_copy);
          ctrl->json_rx += to_copy;
          i += to_copy;
          if (ctrl->json_rx == ctrl->json_len) {
            // completed json body
            sddf_printf(
                "\n[iperf3] ===== Received server results JSON (%u bytes) =====\n%s\n"
                "[iperf3] ================================================\n",
                ctrl->json_len,
                ctrl->result_json
            );

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
    ctrl->pcb = NULL;
}

void iperf_timer_tick(iperf_ctrl_t *ctrl, uint32_t now_ms) {
  if (ctrl->test_active && !ctrl->test_done && now_ms >= ctrl->end_time_ms) {
    ctrl->test_done = true;
  }
  if (ctrl->test_active && now_ms >= ctrl->omit_end_ms) {
    ctrl->omitting = false;
  }
} 

err_t iperf_poll(void *arg, struct tcp_pcb *tpcb) {
    iperf_ctrl_t *ctrl = (iperf_ctrl_t *)arg;
    uint32_t now = sddf_timer_time_now(timer_config.driver_id) / 1000000;
    iperf_timer_tick(ctrl, now);
    if (ctrl->test_done && !ctrl->sent_test_end) {
        for (int i = 0; i < MAX_STREAMS; i++) {
          ctrl->bytes_sent += ctrl->streams[i].bytes;
          ctrl->streams[i].phase = STOPPED;
        }
        ctrl->sent_test_end = true;
        iperf_set_send_state(ctrl, TEST_END);
        
        return ERR_OK;
    }
    return ERR_OK;
}

err_t iperf_ctrl_connect(void *arg,struct tcp_pcb *pcb,
                          err_t err) {
    
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

    // send cookie immediately on connect
    iperf3_ctrl_maybe_tx(ctrl);
    ctrl->rx_phase = CTRL_WAIT_STATE;
    return ERR_OK;
}