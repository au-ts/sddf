#ifndef IPERF3_CTRL_H
#define IPERF3_CTRL_H

#include <stdint.h>
#include <stdbool.h>
#include "lwip/tcp.h"
#include "lwip/ip_addr.h"

#include "iperf3_stream.h"

#define IPERF3_COOKIE_LEN 37
#define MAX_STREAMS 100
#define PAYLOAD_SIZE 16384

typedef enum { 
  CTRL_WAIT_STATE, // 1 BYTE STATE FROM SERVER
  CTRL_WAIT_JSON_LEN, 
  CTRL_WAIT_JSON_BODY,
  CTRL_TEST_RUNNING,
  CTRL_TEST_END,
  CTRL_TEST_RESULTS,
  CTRL_DONE
} ctrl_rx_phase_t;

typedef struct iperf_ctrl {
  struct tcp_pcb *pcb;
  uint8_t cookie[IPERF3_COOKIE_LEN];
  iperf3_stream_t streams[MAX_STREAMS];
  // uint8_t cookie_rx;
  ctrl_rx_phase_t rx_phase;
  uint8_t server_state;
  bool state_ready;
  uint32_t json_len;
  uint32_t json_rx;
  uint16_t server_port;
  ip_addr_t server_addr;


  uint8_t json_len_buf[4];
  uint8_t json_len_rx;
  uint8_t payload[PAYLOAD_SIZE];
  uint8_t result_json[65536];

  uint8_t num_streams;

  uint64_t bytes_sent;

  // tx state
  const int8_t *tx_buf;
  uint16_t tx_len;
  uint16_t tx_off;

  bool test_done;

  bool test_active;
  bool sent_test_end;

  //
  uint32_t omit_ms;
  uint32_t omit_end_ms;
  uint32_t omitting;


  uint32_t duration_ms;
  uint32_t end_time_ms;
  //timers??

  //
  // benchmark_client_config_t bench;
  bool bench_active;
} iperf_ctrl_t;

void iperf3_ctrl_init(iperf_ctrl_t *ctrl);
err_t iperf_ctrl_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err);
err_t iperf_ctrl_sent(void *arg, struct tcp_pcb *tpcb, u16_t len);
void iperf3_ctrl_err(void *arg, err_t err);
err_t iperf_ctrl_connect(void *arg,struct tcp_pcb *pcb, err_t err);

#endif