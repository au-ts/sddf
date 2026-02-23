#ifndef IPERF3_STREAM_H
#define IPERF3_STREAM_H

#include <stdint.h>
#include <stdbool.h>
#include "lwip/tcp.h"
#include "lwip/ip_addr.h"

struct iperf_ctrl;
typedef struct iperf_ctrl iperf_ctrl_t;

typedef enum {
  COOKIE_SEND,
  SEND_PAYLOAD,
  STOPPED
} stream_phase_t;

typedef struct {
  struct tcp_pcb *pcb;
  uint8_t *cookie;


  uint64_t bytes;
  const uint8_t *tx_buf;

  uint16_t tx_len;
  uint16_t tx_off;
  stream_phase_t phase;

  // rx handling for streeam

  iperf_ctrl_t *ctrl; // back reference to ctrl

} iperf3_stream_t;

void iperf3_stream_init(iperf3_stream_t *stream, uint8_t *cookie, iperf_ctrl_t *ctrl);
void iperf3_stream_maybe_tx(iperf3_stream_t *stream);
err_t iperf3_stream_connect(void *arg, struct tcp_pcb *pcb, err_t err);

err_t iperf3_stream_sent(void *arg, struct tcp_pcb *tpcb, u16_t len);
err_t iperf3_stream_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err);
void iperf3_stream_err(void *arg, err_t err);

#endif // IPERF3_STREAM_H
