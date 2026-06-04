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

    stream->rtt_sent = 0;
    stream->rtt_acked = 0;
    stream->rtt_target = 0;
    stream->rtt_t0_ns = 0;
    stream->rtt_pending = false;
    stream->rtt_min_us = 0;
    stream->rtt_max_us = 0;
    stream->rtt_count = 0;
    stream->rtt_sum_us = 0;
    stream->rtt_sumsq_us = 0;
}

// maybe transmit data on this stream - loops to fill the send buffer in one call
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

    if (tcp_write(stream->pcb, stream->tx_buf + stream->tx_off, chunk, TCP_WRITE_FLAG_COPY) != ERR_OK) {
      sddf_printf("[tcp_dbg] tcp_write FAIL sndbuf=%u chunk=%u\n", tcp_sndbuf(stream->pcb), chunk);
      break;
    }

    stream->tx_off += chunk;
    stream->bytes_this_tick += chunk;
    stream->rtt_sent += chunk;
    wrote = true;
  }
  if (wrote) {
    tcp_output(stream->pcb);
    /* Start an RTT sample if none is in flight (one outstanding => ~1 per RTT). */
    if (!stream->rtt_pending && stream->ctrl && !stream->ctrl->omitting) {
      stream->rtt_pending = true;
      stream->rtt_target = stream->rtt_sent;
      stream->rtt_t0_ns = sddf_timer_time_now(timer_config.driver_id);
    }
  }
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

    /* Complete an RTT sample once the timed byte offset has been ACKed. */
    stream->rtt_acked += len;
    if (stream->rtt_pending && stream->rtt_acked >= stream->rtt_target) {
        uint64_t now = sddf_timer_time_now(timer_config.driver_id);
        uint32_t rtt_us = (uint32_t)((now - stream->rtt_t0_ns) / 1000);
        if (stream->rtt_count == 0 || rtt_us < stream->rtt_min_us) stream->rtt_min_us = rtt_us;
        if (rtt_us > stream->rtt_max_us) stream->rtt_max_us = rtt_us;
        stream->rtt_sum_us += rtt_us;
        stream->rtt_sumsq_us += (uint64_t)rtt_us * rtt_us;
        stream->rtt_count++;
        stream->rtt_pending = false;
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