#include "iperf3_stream.h"
#include <sddf/timer/config.h>
#include "iperf3_ctrl.h"
#include <sddf/timer/client.h>



#define IPERF3_COOKIE_LEN 37  
#define CREATE_STREAMS 10
#define TEST_START       1
#define TEST_RUNNING     2

extern timer_client_config_t timer_config;

/**
 * Initialise all stream members
 * 
 * @param stream the stream
 * @param cookie cookie
 * @param ctrl ctrl
 */
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

    stream->rx_bytes = 0;
    stream->is_sender = true;

    /* Server-side receive and pacing state*/
    stream->cookie_rx_len = 0;
    stream->bytes_this_tick = 0;
    stream->tick_byte_limit = 0;
}

/**
 * Maybe transmit data on this stream. Loops and tcp_writes until pcb is full
 * If write was successful then we increment relevant counters and start an
 * RTT sample and was for an acknowledgement for that batch if a sample is not
 * already active
 * 
 * @param stream stream to transmit on
 * 
 */
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
      sddf_printf(" tcp_write FAIL sndbuf=%u chunk=%u\n", tcp_sndbuf(stream->pcb), chunk);
      break;
    }

    stream->tx_off += chunk;
    stream->bytes_this_tick += chunk;
    stream->rtt_sent += chunk;
    wrote = true;
  }
  if (wrote) {
    tcp_output(stream->pcb);
    /* Start an RTT sample */
    if (!stream->rtt_pending && stream->ctrl && !stream->ctrl->omitting) {
      stream->rtt_pending = true;
      stream->rtt_target = stream->rtt_sent;
      stream->rtt_t0_ns = sddf_timer_time_now(timer_config.driver_id);
    }
  }
}

/**
 * Try to connect TCP data stream to the server. Initialise callbacks then queue
 * and send the cookie
 * 
 * @param arg stream
 * @param tpcb tcp_pcb for the underlying stream connection
 * @param err 
 * 
 */
err_t iperf3_stream_connect(void *arg, struct tcp_pcb *tpcb, err_t err) {
    iperf3_stream_t *s = (iperf3_stream_t *)arg;
    if (err != ERR_OK) return err;

    s->pcb = tpcb;
    tcp_arg(tpcb, s);
    tcp_sent(tpcb, iperf3_stream_sent);
    tcp_recv(tpcb, iperf3_stream_recv);
    tcp_err(tpcb, iperf3_stream_err);

    // queue cookie to send on this stream
    s->tx_buf = (const uint8_t *)s->cookie;
    s->tx_len = IPERF3_COOKIE_LEN;
    s->tx_off = 0;
    iperf3_stream_maybe_tx(s);

    s->phase = COOKIE_SEND;
    return ERR_OK;
}

/**
 * Callback for tcp_sent. When acks arrive calculate rtt stats. TCP segs are freed
 * from lwips pbufs and we try send mroe data via maybe_tx
 * 
 * @param arg stream 
 * @param tpcb tcp_pcb for the underlying stream connection
 * @param len number of payload bytes that the peer acknowledged
 * 
 */
err_t iperf3_stream_sent(void *arg, struct tcp_pcb *tpcb, u16_t len) {
    iperf3_stream_t *stream = (iperf3_stream_t *)arg;
    (void)tpcb;
    if (!stream->ctrl->omitting) {
        stream->bytes += len;
    }

    /* rtt sample */
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


/**
 * Receive callback for server data stream which checks omitting and validates 
 * cookie. Then sends cookie reply back via iperf3_server_stream_ready and
 * frees pbufs
 * 
 * @param arg stream handle
 * @param tpcb tcp_pcb
 * @param p pbuf for received data
 * @param err error
 * 
 */
err_t iperf3_server_stream_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err) {
    iperf3_stream_t *stream = (iperf3_stream_t *)arg;
    iperf_ctrl_t *ctrl = stream->ctrl;

    if (err != ERR_OK) {
        return err;
    }
    if (p == NULL) {
        stream->pcb = NULL;
        return ERR_OK;
    }

    /* if warming up keep resetting */
    if (ctrl->omitting) {
        uint32_t now_ms = sddf_timer_time_now(timer_config.driver_id) / 1000000;
        if (now_ms >= ctrl->omit_end_ms) {
            for (int s = 0; s < MAX_STREAMS; s++) {
                ctrl->streams[s].rx_bytes = 0;
            }
            ctrl->omitting = false;
        }
    }

    struct pbuf *q = p;
    while (q != NULL) {
        uint8_t *data = (uint8_t *)q->payload;
        uint16_t n = q->len;
        uint16_t i = 0;
        while (stream->cookie_rx_len < IPERF3_COOKIE_LEN && i < n) {

            // error check
            if (data[i] != ctrl->cookie[stream->cookie_rx_len]) {
                sddf_printf("[iperf3] stream cookie mismatch at byte %u\n",
                            (unsigned)stream->cookie_rx_len);
            }
            stream->cookie_rx_len++;
            i++;
            if (stream->cookie_rx_len == IPERF3_COOKIE_LEN) {
                iperf3_server_stream_ready(ctrl);
            }
        }

        /* Everything after the cookie is measured */
        stream->rx_bytes += (uint64_t)(n - i);
        q = q->next;
    }

    tcp_recved(tpcb, p->tot_len);
    pbuf_free(p);
    return ERR_OK;
}


/**
 * Receive callback for client data stream which just accumulates totals and 
 * frees pbufs after
 * 
 * @param arg stream handle
 * @param tpcb tcp_pcb
 * @param p pbuf for received data
 * @param err error
 * 
 */
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


    if (!stream->is_sender && !stream->ctrl->omitting) {
      stream->rx_bytes += p->tot_len;
    }

    /* Tell lwIP we consumed the data */
    tcp_recved(tpcb, p->tot_len);
    pbuf_free(p);
    return ERR_OK;
}

void iperf3_stream_err(void *arg, err_t err) {
    iperf3_stream_t *stream = (iperf3_stream_t *)arg;
    stream->pcb = NULL;
}