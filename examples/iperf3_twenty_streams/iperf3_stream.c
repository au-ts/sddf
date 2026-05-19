#include "iperf3_stream.h"
#include <sddf/timer/config.h>
#include "iperf3_ctrl.h"
#include <sddf/timer/client.h>

#define IPERF3_COOKIE_LEN 37  

extern timer_client_config_t timer_config;

void iperf3_stream_init(iperf3_stream_t *stream, uint8_t *cookie, iperf_ctrl_t *ctrl) {
    stream->pcb = NULL;
    stream->cookie = cookie;
    stream->tx_buf = NULL;
    stream->tx_len = 0;
    stream->tx_off = 0;
    stream->phase = COOKIE_SEND;
    stream->ctrl = ctrl;
    stream->bytes = 0;
}

void iperf3_stream_maybe_tx(iperf3_stream_t *stream) {
  if (stream->pcb == NULL) return;
  if (stream->phase == STOPPED) return;
  if (stream->phase == SEND_PAYLOAD) {
    iperf_ctrl_t *c = stream->ctrl;
    if (c == NULL) return;
    // note that this decreased throughput a lot. maybe kind of expensive
    // also sddfprint decreased throughput a lot
    // uint32_t now_ms = sddf_timer_time_now(timer_config.driver_id) / 1000000;
    // if (now_ms >= c->end_time_ms) {
    //   c->rx_phase = CTRL_TEST_END;
    //   stream->phase = STOPPED;

    //   return;
    // }
  }
  if (stream->tx_buf == NULL) return; 
  if (stream->tx_len == stream->tx_off && stream->phase == SEND_PAYLOAD) {
    stream->tx_off = 0;
  }

  if (stream->tx_len == stream->tx_off && stream->phase != SEND_PAYLOAD) {
    return;
  }
  // ask how much space

  u16_t avail = tcp_sndbuf(stream->pcb);
  if (avail == 0) return;
  // compete chunk 
  u16_t remaining = stream->tx_len - stream->tx_off;
  u16_t chunk = remaining > avail ? avail : remaining;
  // try to enqueue
  err_t err = tcp_write(stream->pcb, stream->tx_buf + stream->tx_off, chunk, TCP_WRITE_FLAG_COPY);

  // if (err return
  if (err != ERR_OK) {

    return;
  }
  // advance progress
  stream->tx_off += chunk;
  // flush
  tcp_output(stream->pcb);
}

 err_t iperf3_stream_connect(void *arg, struct tcp_pcb *tpcb, err_t err) {
    iperf3_stream_t *s = (iperf3_stream_t *)arg;
    if (err != ERR_OK) return err;

    s->pcb = tpcb;
    tcp_arg(tpcb, s);
    tcp_sent(tpcb, iperf3_stream_sent);
    tcp_recv(tpcb, iperf3_stream_recv);   // can be NULL if you truly never read
    tcp_err(tpcb, iperf3_stream_err);

    // queue cookie to send on this stream
    s->tx_buf = (const uint8_t *)s->cookie;
    s->tx_len = IPERF3_COOKIE_LEN;
    s->tx_off = 0;
    iperf3_stream_maybe_tx(s);

    s->phase = COOKIE_SEND;
    return ERR_OK;
}
err_t iperf3_stream_sent(void *arg, struct tcp_pcb *tpcb, u16_t len) {
    iperf3_stream_t *stream = (iperf3_stream_t *)arg;
    (void)tpcb;
    if (!stream->ctrl->omitting) {
      stream->bytes += len;

    }
    iperf3_stream_maybe_tx(stream);
    return ERR_OK;
}

err_t iperf3_stream_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err) {
    iperf3_stream_t *stream = (iperf3_stream_t *)arg;
    (void)stream;
    (void)tpcb;

    if (err != ERR_OK) {
      return err;
    }

    if (p == NULL) {
        stream->pcb = NULL;
        return ERR_OK;
    }

    // process received data in pbuf chain p

    pbuf_free(p);
    return ERR_OK;
}

void iperf3_stream_err(void *arg, err_t err) {
    iperf3_stream_t *stream = (iperf3_stream_t *)arg;
    stream->pcb = NULL;
}