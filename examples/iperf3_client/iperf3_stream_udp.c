#include "iperf3_stream.h"
#include <sddf/timer/config.h>
#include "iperf3_ctrl.h"
#include <sddf/timer/client.h>
#include <lwip/udp.h>

#define UDP_CONNECT_REPLY 0x39383736

extern timer_client_config_t timer_config;

void udp_pump(iperf3_udp_stream_t *stream) {
  if (!stream || !stream->pcb || stream->phase != SEND_PAYLOAD) return;
  if (stream->ctrl && stream->ctrl->is_reverse) return;

  while (stream->packets_this_tick < stream->burst_max) {
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

    /* iperf3 UDP datagram header (16 bytes):
     *   [0-3]  tv_sec  (big-endian)
     *   [4-7]  tv_usec (big-endian)
     *   [8-11] id      lower 32 bits of packet counter (big-endian, signed)
     *   [12-15] id2    upper 32 bits of packet counter (big-endian)
     */
    const uint16_t hdr_len = 16;

    uint32_t sec_be  = htonl(sec);
    uint32_t usec_be = htonl(usec);
    uint32_t id      = htonl(seq); 
    uint32_t id2     = htonl(0);

    memcpy(buf + 0,  &sec_be,  4);
    memcpy(buf + 4,  &usec_be, 4);
    memcpy(buf + 8,  &id,      4);
    memcpy(buf + 12, &id2,     4);


    memcpy(buf + hdr_len, stream->tx_buf, stream->payload_len - hdr_len);
    err_t err = udp_sendto(stream->pcb, p, &stream->server_addr, stream->server_port);
    pbuf_free(p);
    if (err == ERR_MEM) {
      break; /* TX ring full; retry next tick */
    }
    if (err != ERR_OK) {
      sddf_printf("[udp] sendto err=%d seq=%u\n", (int)err, seq);
      break;
    }
    stream->seq_num++;
    stream->packets_sent++;
    stream->packets_this_tick++;
    if (!(stream->ctrl && stream->ctrl->omitting)) stream->bytes_sent += stream->payload_len;
  }
}

void udp_stream_recv(void *arg, struct udp_pcb *pcb, struct pbuf *p,
                     const ip_addr_t *addr, u16_t port) {
    iperf3_udp_stream_t *stream = (iperf3_udp_stream_t *)arg;
    (void)pcb; (void)addr; (void)port;

    if (!p) return;
    iperf_ctrl_t *ctrl = stream->ctrl;

    /* Connect handshake */
    if (p->len >= 4) {
        uint32_t reply;
        memcpy(&reply, p->payload, sizeof(reply));
        if (reply == UDP_CONNECT_REPLY || ntohl(reply) == UDP_CONNECT_REPLY) {
            stream->phase = SEND_PAYLOAD;   /* forward mode begin pumping */
            pbuf_free(p);
            return;
        }
    }
    

    if (ctrl && !stream->is_sender && !ctrl->omitting && p->len >= 16) {
        uint8_t *b = (uint8_t *)p->payload;
        uint32_t sec_be, usec_be, seq_be;
        memcpy(&sec_be,  b + 0, 4);
        memcpy(&usec_be, b + 4, 4);
        memcpy(&seq_be,  b + 8, 4);
        uint32_t sec  = ntohl(sec_be);
        uint32_t usec = ntohl(usec_be);
        uint32_t seq  = ntohl(seq_be);

        stream->rx_bytes += p->tot_len;
        stream->rx_packets++;
        if (!stream->rx_have_first) {
            stream->rx_have_first = 1;
            stream->rx_first_seq = seq;
        }
        if (seq > stream->rx_last_seq) stream->rx_last_seq = seq;

        /* RFC1889 interarrival jitter */
        uint64_t now_ns = sddf_timer_time_now(timer_config.driver_id);
        double arrival = (double)now_ns / 1e9;
        double sent = (double)sec + (double)usec / 1e6;
        double transit = arrival - sent;
        if (stream->rx_packets > 1) {
            double d = transit - stream->rx_prev_transit;
            if (d < 0) d = -d;
            stream->rx_jitter += (d - stream->rx_jitter) / 16.0;

        }
        stream->rx_prev_transit = transit;
    }

    pbuf_free(p);
}
