#include "iperf3_stream.h"
#include <sddf/timer/config.h>
#include "iperf3_ctrl.h"
#include <sddf/timer/client.h>
#include <lwip/udp.h>

#define UDP_CONNECT_REPLY 0x39383736
#define UDP_CONNECT_MSG 0x36373839

extern timer_client_config_t timer_config;

void udp_pump(iperf3_udp_stream_t *stream) {
  if (!stream || !stream->pcb || stream->phase != SEND_PAYLOAD) return;

  if (!stream->is_sender) return;

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
    err_t err = udp_sendto(stream->pcb, p, &stream->peer_addr, stream->peer_port);
    pbuf_free(p);
    if (err == ERR_MEM) {
      break;
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

/* Acknowledge a stream handshake */
static void udp_send_connect_reply(struct udp_pcb *pcb, const ip_addr_t *addr, u16_t port) {
    struct pbuf *pb = pbuf_alloc(PBUF_TRANSPORT, sizeof(uint32_t), PBUF_RAM);
    if (!pb) {
        sddf_printf("[udp] reply pbuf_alloc failed\n");
        return;
    }

    uint32_t reply = UDP_CONNECT_REPLY;
    memcpy(pb->payload, &reply, sizeof(reply));
    err_t err = udp_sendto(pcb, pb, addr, port);
    pbuf_free(pb);
    if (err != ERR_OK) sddf_printf("[udp] reply send err=%d\n", (int)err);
}

static bool udp_is_connect_msg(struct pbuf *p) {
    if (p->len < 4) return false;
    uint32_t msg;
    memcpy(&msg, p->payload, sizeof(msg));
    return (msg == UDP_CONNECT_MSG || ntohl(msg) == UDP_CONNECT_MSG);
}

struct udp_pcb *udp_new_listener(iperf_ctrl_t *ctrl) {
    struct udp_pcb *pcb = udp_new();
    if (pcb == NULL) {
        sddf_printf("[udp] udp_new failed\n");
        return NULL;
    }
    
    ip_set_option(pcb, SOF_REUSEADDR);
    uint16_t dport = ctrl->server_port ? ctrl->server_port : 5202;
    err_t err = udp_bind(pcb, IP4_ADDR_ANY, dport);
    if (err != ERR_OK) {
        sddf_printf("[udp] bind %u failed: %d\n", dport, (int)err);
        udp_remove(pcb);
        return NULL;
    }
    udp_recv(pcb, udp_listener_recv, ctrl);
    return pcb;
}

/**
 * the listener pcb is converted into this client's stream pcb and
 * a replacement listener is bound to the same port for the next stream.
 *
 * @param arg the control block
 * @param pcb the listener pcb, about to become a stream pcb
 * @param p pbuf containing the setup datagram
 * @param addr ip address of the peer
 * @param port source port of the peer
 *
**/
void udp_listener_recv(void *arg, struct udp_pcb *pcb, struct pbuf *p,
                       const ip_addr_t *addr, u16_t port) {
    iperf_ctrl_t *ctrl = (iperf_ctrl_t *)arg;
    if (!p) return;
    if (!ctrl) { pbuf_free(p); return; }

    /* How many streams we expect in each direction */
    uint8_t to_rec  = ctrl->is_bidirectional ? ctrl->num_streams
                                             : (ctrl->is_reverse ? 0 : ctrl->num_streams);
    uint8_t to_send = ctrl->is_bidirectional ? ctrl->num_streams
                                             : (ctrl->is_reverse ? ctrl->num_streams : 0);
    uint8_t total   = to_rec + to_send;
    uint8_t claimed = ctrl->rec_streams_accepted + ctrl->send_streams_accepted;

    if (!udp_is_connect_msg(p) || claimed >= total || claimed >= MAX_STREAMS) {
        pbuf_free(p);   /* stray traffic on the listener */
        return;
    }

    /* Direction is assigned by arrival order */
    bool as_sender;
    if (ctrl->rec_streams_accepted < to_rec) {
        as_sender = false;
        ctrl->rec_streams_accepted++;
    } else {
        as_sender = true;
        ctrl->send_streams_accepted++;
    }

    /* Promote the listener into this clients stream. */
    uint8_t s = claimed;
    iperf3_udp_stream_t *stream = &ctrl->udp_streams[s];
    stream->ctrl = ctrl;
    stream->pcb = pcb;
    stream->peer_addr = *addr;
    stream->peer_port = port;
    stream->is_sender = as_sender;
    stream->phase = STOPPED;

    if (udp_connect(pcb, addr, port) != ERR_OK) {
        sddf_printf("[udp] connect stream %u failed\n", s);
    }
    udp_recv(pcb, udp_stream_recv, stream);
    claimed++;
    sddf_printf("[udp] stream %u/%u from port %u (%s)\n",
                claimed, total, port, as_sender ? "TX" : "RX");

    ctrl->udp_listen = (claimed < total) ? udp_new_listener(ctrl) : NULL;

    udp_send_connect_reply(pcb, addr, port);
    pbuf_free(p);

    if (claimed == total) {
        iperf3_udp_server_start(ctrl);
    }
}

/**
 * Data path for an established stream.
 * 
 * @param arg udp stream handle
 * @param pcb pcb containing the underlying connection
 * @param p pbuf containing the msg/data from the peer
 * @param addr ip address of the peer
 * @param port port of the peer
 *
**/
void udp_stream_recv(void *arg, struct udp_pcb *pcb, struct pbuf *p,
                     const ip_addr_t *addr, u16_t port) {
    iperf3_udp_stream_t *stream = (iperf3_udp_stream_t *)arg;
    (void)pcb;

    if (!p) return;
    if (!stream || !stream->ctrl) { pbuf_free(p); return; }
    iperf_ctrl_t *ctrl = stream->ctrl;

    if (ctrl->role == 's') {
      if (udp_is_connect_msg(p)) {
        udp_send_connect_reply(stream->pcb, addr, port);
        pbuf_free(p);
        return;
      }
    } else if (p->len >= 4) {
      /* Connect handshake */
      uint32_t reply;
      memcpy(&reply, p->payload, sizeof(reply));
      if (reply == UDP_CONNECT_REPLY || ntohl(reply) == UDP_CONNECT_REPLY) {
        stream->phase = SEND_PAYLOAD;   /* forward mode begin pumping */
        pbuf_free(p);
        return;
      }
    }

    if (!stream->is_sender && !ctrl->omitting && p->len >= 16) {
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
