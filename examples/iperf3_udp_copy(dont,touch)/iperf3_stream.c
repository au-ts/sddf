#include "iperf3_stream.h"
#include <sddf/timer/config.h>
#include "iperf3_ctrl.h"
#include <sddf/timer/client.h>
#include <lwip/udp.h>

#define IPERF3_COOKIE_LEN 37  

#define UDP_CONNECT_MSG 0x36373839 
#define UDP_CONNECT_REPLY 0x39383736

static uint64_t to_be64(uint64_t x) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    return ((uint64_t)htonl((uint32_t)(x & 0xFFFFFFFFULL)) << 32) |
           htonl((uint32_t)(x >> 32));
#else
    return x;
#endif
}

extern timer_client_config_t timer_config;

// initialise all stream state members
void iperf3_stream_init(iperf3_stream_t *stream, uint8_t *cookie, iperf_ctrl_t *ctrl) {
    stream->pcb = NULL;
    stream->cookie = cookie;
    stream->tx_buf = NULL;
    stream->tx_len = 0;
    stream->tx_off = 0;
    stream->phase = MESSAGE_SEND;
    stream->ctrl = ctrl;
    stream->bytes = 0;
}

// maybe transmit data on this stream
void iperf3_stream_maybe_tx(iperf3_stream_t *stream) {
  if (stream->pcb == NULL) return;
  if (stream->phase == STOPPED) return;
  if (stream->phase == SEND_PAYLOAD) {
    iperf_ctrl_t *c = stream->ctrl;
    if (c == NULL) return;
  }

  if (stream->tx_buf == NULL) return; 
  if (stream->tx_len == stream->tx_off && stream->phase == SEND_PAYLOAD) {
    stream->tx_off = 0; // loop payload until STOPPED
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

void udp_pump(iperf3_udp_stream_t *stream) {
  if (!stream || !stream->pcb || stream->phase != SEND_PAYLOAD) return;

  uint32_t sent = 0;
  uint32_t failed = 0;
  for (int i = 0; i < stream->burst_max; i++) {
    // time
    struct pbuf *p = pbuf_alloc(PBUF_TRANSPORT, stream->payload_len, PBUF_RAM);
    if (!p) {
      sddf_printf("[udp] pbuf_alloc failed\n");
      break;
    }
    uint64_t now_ns = sddf_timer_time_now(timer_config.driver_id);
    uint32_t sec  = (uint32_t)(now_ns / 1000000000ULL);

    uint32_t usec = (uint32_t)((now_ns % 1000000000ULL) / 1000);
    uint8_t *buf = p->payload;
    uint32_t seq = stream->seq_num + 1;

    // 64 bit seq num, 32 bit sec, 32 bit usec, rest is payload data (need to be at least 16 bytes for header)  
    // idk
    // says datagrams received all out of order
    const uint16_t hdr_len = 16;

    uint32_t sec_be  = htonl(sec);
    uint32_t usec_be = htonl(usec);
    uint64_t seq_be  = to_be64((uint64_t)seq);

    memcpy(buf + 0, &sec_be,  4);
    memcpy(buf + 4, &usec_be, 4);
    memcpy(buf + 8, &seq_be,  8);


    memcpy(buf + hdr_len, stream->tx_buf, stream->payload_len - hdr_len);
    // sddf_printf("seq=%llu bytes=%02x %02x %02x %02x %02x %02x %02x %02x\n",
    // seq,
    // buf[8], buf[9], buf[10], buf[11],
    // buf[12], buf[13], buf[14], buf[15]);
    err_t err = udp_sendto(stream->pcb, p, &stream->server_addr, stream->server_port);
    pbuf_free(p);
    if (err != ERR_OK) {
      sddf_printf("[udp] sendto err=%d seq=%u\n", (int)err, seq);
      failed++;
      break;
    }
    stream->seq_num++;
    stream->packets_sent++;
    sent++;
    if (!(stream->ctrl && stream->ctrl->omitting)) stream->bytes_sent += stream->payload_len;
  }
  // sddf_printf("[udp] pump done: sent=%u failed=%u seq_now=%u\n", sent, failed, (uint32_t)stream->seq_num);
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

    // send msg

    uint32_t msg = htonl(UDP_CONNECT_MSG);
    s->tx_buf = (const uint8_t *)&msg;
    s->tx_len = sizeof(msg);
    s->tx_off = 0;
    iperf3_stream_maybe_tx(s);

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

void udp_stream_recv(void *arg, struct udp_pcb *pcb, struct pbuf *p,
                     const ip_addr_t *addr, u16_t port) {
    iperf3_udp_stream_t *stream = (iperf3_udp_stream_t *)arg;

    if (!p) return;

    sddf_printf("[udp recv] got packet len=%u from port=%u\n", p->tot_len, port);

    if (p->len >= 4) {
        uint32_t reply;
        memcpy(&reply, p->payload, sizeof(reply));

        sddf_printf("[udp recv] reply raw=0x%08x ntohl=0x%08x\n",
                    reply, ntohl(reply));

        if (reply == UDP_CONNECT_REPLY || ntohl(reply) == UDP_CONNECT_REPLY) {
            sddf_printf("[udp] received connect reply\n");
            stream->phase = SEND_PAYLOAD;
        }
    }

    pbuf_free(p);
}