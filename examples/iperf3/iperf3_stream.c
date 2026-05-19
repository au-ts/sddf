#include "iperf3_stream.h"
#include <sddf/timer/config.h>
#include "iperf3_ctrl.h"
#include <sddf/timer/client.h>

#define IPERF3_COOKIE_LEN 37  

extern timer_client_config_t timer_config;

// initialise all stream state members
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

// maybe transmit data on this stream — loops to fill the send buffer in one call
void iperf3_stream_maybe_tx(iperf3_stream_t *stream) {
  if (stream->pcb == NULL) return;
  if (stream->phase == STOPPED) return;
  if (stream->phase == SEND_PAYLOAD && stream->ctrl == NULL) return;
  if (stream->tx_buf == NULL) return;

  bool wrote = false;
  for (;;) {
    if (stream->tick_byte_limit > 0 && stream->bytes_this_tick >= stream->tick_byte_limit) break;

    if (stream->tx_off == stream->tx_len) {
      if (stream->phase == SEND_PAYLOAD) {
        stream->tx_off = 0;
      } else {
        break;
      }
    }

    u16_t avail = tcp_sndbuf(stream->pcb);
    if (avail == 0) break;

    u16_t remaining = stream->tx_len - stream->tx_off;
    u16_t chunk = remaining > avail ? avail : remaining;
    if (stream->tick_byte_limit > 0) {
      uint32_t budget = stream->tick_byte_limit - stream->bytes_this_tick;
      if ((uint32_t)chunk > budget) chunk = (u16_t)budget;
    }
    if (chunk == 0) break;

    if (tcp_write(stream->pcb, stream->tx_buf + stream->tx_off, chunk, TCP_WRITE_FLAG_COPY) != ERR_OK) break;

    stream->tx_off += chunk;
    stream->bytes_this_tick += chunk;
    wrote = true;
  }
  if (wrote) tcp_output(stream->pcb);
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