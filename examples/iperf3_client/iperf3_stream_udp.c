/*
 * UDP data-path helpers. The TCP stream callbacks live in iperf3_stream_tcp.c;
 * both files are compiled into every image now that protocol is a runtime choice
 * (`start [tcp|udp] ...`), so this file must only define the UDP-specific
 * functions to avoid duplicate symbols.
 */
#include "iperf3_stream.h"
#include <sddf/timer/config.h>
#include "iperf3_ctrl.h"
#include <sddf/timer/client.h>
#include <lwip/udp.h>

#define UDP_CONNECT_REPLY 0x39383736

extern timer_client_config_t timer_config;

void udp_pump(iperf3_udp_stream_t *stream) {
  if (!stream || !stream->pcb || stream->phase != SEND_PAYLOAD) return;

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
    uint32_t id      = htonl(seq);          /* lower 32 bits */
    uint32_t id2     = htonl(0);            /* upper 32 bits (always 0 for seq < 2^32) */

    memcpy(buf + 0,  &sec_be,  4);
    memcpy(buf + 4,  &usec_be, 4);
    memcpy(buf + 8,  &id,      4);
    memcpy(buf + 12, &id2,     4);


    memcpy(buf + hdr_len, stream->tx_buf, stream->payload_len - hdr_len);
    err_t err = udp_sendto(stream->pcb, p, &stream->server_addr, stream->server_port);
    pbuf_free(p);
    if (err == ERR_MEM) {
      break; /* TX ring full; retry next tick (seq_num not incremented = no gap) */
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
