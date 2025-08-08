/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <os/sddf.h>

#include "echo.h"
#include "lwip/ip.h"
#include "lwip/pbuf.h"
#include "lwip/tcp.h"

#include <sddf/util/util.h>

/* At most ECHO_QUEUE_CAPACITY - 1 bytes can be in the queue */
#define ECHO_QUEUE_CAPACITY (TCP_WND + 1)

/* The echo state stores received data to be echoed back in a circular buffer.
Data is written to the tail index, and transmitted from the ack_head in FIFO
order. Data from ack_head to tcp_write_head has been transmitted succesfully
with `tcp_write` and is awaiting acknowledgement. When the data is acknowledged,
ack_head is incremented. Data from tcp_write_head to tail is awaiting successful
transmission with `tcp_write`. tcp_write_head must always lie between ack_head
and tail: ack_head <= tcp_write_head <= tail (assuming no roll-over) */
struct echo_state {
    bool in_use;
    size_t tail; /* Data is in inserted at the tail when received */
    size_t tcp_write_head; /* Next data to be transmitted with TCP write */
    size_t ack_head; /* Next data awaiting acknowledgemet */
    char buf[ECHO_QUEUE_CAPACITY];
};

static struct echo_state tcp_state_pool[TCP_ECHO_MAX_CONNS];

static struct echo_state *tcp_state_alloc()
{
    for (int i = 0; i < TCP_ECHO_MAX_CONNS; ++i) {
        if (!tcp_state_pool[i].in_use) {
            tcp_state_pool[i].in_use = true;
            return &tcp_state_pool[i];
        }
    }
    return NULL;
}

static void tcp_state_free(struct echo_state *state)
{
    assert(state);
    assert(state->in_use);
    state->in_use = false;
}

static inline size_t tcp_state_avail(struct echo_state *state)
{
    return (state->ack_head - state->tail + ECHO_QUEUE_CAPACITY - 1) % ECHO_QUEUE_CAPACITY;
}

static inline size_t tcp_state_cont_avail(struct echo_state *state)
{
    /* Eliminate case head == 0, tail == capacity - 1 */
    if (!tcp_state_avail(state)) {
        return 0;
    }

    if (state->tail >= state->ack_head && state->ack_head != 0) {
        return ECHO_QUEUE_CAPACITY - state->tail;
    }

    return state->ack_head - state->tail - 1;
}

static inline size_t tcp_state_len_to_tx(struct echo_state *state)
{
    return (state->tail - state->tcp_write_head + ECHO_QUEUE_CAPACITY) % ECHO_QUEUE_CAPACITY;
}

static inline size_t tcp_state_cont_len_to_tx(struct echo_state *state)
{
    if (state->tail >= state->tcp_write_head) {
        return state->tail - state->tcp_write_head;
    }
    return ECHO_QUEUE_CAPACITY - state->tcp_write_head;
}

static inline size_t tcp_state_len_unacked(struct echo_state *state)
{
    return (state->tcp_write_head - state->ack_head + ECHO_QUEUE_CAPACITY) % ECHO_QUEUE_CAPACITY;
}

static err_t tcp_echo_sent(void *arg, struct tcp_pcb *pcb, u16_t len)
{
    struct echo_state *state = arg;
    assert(state != NULL);
    assert(len <= tcp_state_len_unacked(state));

    state->ack_head = (state->ack_head + len) % ECHO_QUEUE_CAPACITY;

    /* tcp_recved is only for increasing the TCP window, and isn't required to
    ACK incoming packets (that is done automatically on receive). */
    tcp_recved(pcb, len);

    return ERR_OK;
}

static err_t tcp_echo_recv(void *arg, struct tcp_pcb *pcb, struct pbuf *p, err_t err)
{
    struct echo_state *state = arg;
    assert(state != NULL);

    if (p == NULL) {
        /* closing */
        sddf_printf("tcp_echo[%s:%d]: closing\n",
                    ipaddr_ntoa(&pcb->remote_ip), pcb->remote_port
                   );

        tcp_state_free(state);
        tcp_arg(pcb, NULL);

        err = tcp_close(pcb);
        if (err) {
            sddf_printf("tcp_echo[%s:%d]: close error: %s\n",
                        ipaddr_ntoa(&pcb->remote_ip), pcb->remote_port,
                        lwip_strerr(err)
                       );
            return err;
        }
        return ERR_OK;
    }
    if (err) {
        sddf_printf("tcp_echo[%s:%d]: recv error: %s\n",
                    ipaddr_ntoa(&pcb->remote_ip), pcb->remote_port,
                    lwip_strerr(err)
                   );
        return err;
    }

    assert(p->tot_len > 0);

    const size_t capacity = MIN(MIN(tcp_state_avail(state), tcp_sndbuf(pcb)), p->tot_len);
    if (p->tot_len > capacity) {
        sddf_printf("tcp_echo[%s:%d]: can't handle packet of %d bytes: queue_space=%lu sndbuf=%d snd_queuelen=%d\n",
                    ipaddr_ntoa(&pcb->remote_ip), pcb->remote_port, p->tot_len, tcp_state_avail(state), tcp_sndbuf(pcb),
                    pcb->snd_queuelen);

        /* This causes LWIP to wait a bit and try calling this function again
        with the packet. To avoid double-sending any data in the packet, we
        don't handle the packet at all, even if we would have space for part
        of it. */
        return ERR_MEM;
    }

    /* Copy received data into tcp state */
    size_t offset = 0;
    while (offset < capacity) {
        const u16_t copied_len = pbuf_copy_partial(p, state->buf + state->tail,
                                                   MIN(tcp_state_cont_avail(state), capacity - offset), offset);

        offset += copied_len;
        state->tail = (state->tail + copied_len) % ECHO_QUEUE_CAPACITY;
    }

    /* Attempt to transmit more data */
    size_t len_to_tx = tcp_state_len_to_tx(state);
    while (len_to_tx) {
        size_t tx_batch = MIN(UINT16_MAX, tcp_state_cont_len_to_tx(state));
        err = tcp_write(pcb, state->buf + state->tcp_write_head, tx_batch, 0);
        if (err) {
            /* Retry later */
            break;
        }
        state->tcp_write_head = (state->tcp_write_head + tx_batch) % ECHO_QUEUE_CAPACITY;
        len_to_tx = tcp_state_len_to_tx(state);
    }

    tcp_output(pcb);

    pbuf_free(p);
    return ERR_OK;
}

static void tcp_echo_err(void *arg, err_t err)
{
    struct echo_state *state = arg;
    assert(state != NULL);

    sddf_printf("tcp_echo: %s\n", lwip_strerr(err));

    tcp_state_free(state);
}

static err_t tcp_echo_accept(void *arg, struct tcp_pcb *pcb, err_t err)
{
    struct echo_state *state = tcp_state_alloc();
    if (state == NULL) {
        sddf_printf("tcp_echo: failed to alloc state\n");
        return ERR_MEM;
    }

    sddf_printf("tcp_echo[%s:%d]: accept\n",
                ipaddr_ntoa(&pcb->remote_ip), pcb->remote_port
               );

    state->tail = 0;
    state->ack_head = 0;
    state->tcp_write_head = 0;

    tcp_nagle_disable(pcb);
    tcp_arg(pcb, state);
    tcp_sent(pcb, tcp_echo_sent);
    tcp_recv(pcb, tcp_echo_recv);
    tcp_err(pcb, tcp_echo_err);

    return ERR_OK;
}

int setup_tcp_socket(void)
{
    struct tcp_pcb *pcb;

    pcb = tcp_new_ip_type(IPADDR_TYPE_V4);
    if (pcb == NULL) {
        sddf_printf("Failed to open TCP echo socket\n");
        return -1;
    }

    err_t error = tcp_bind(pcb, IP_ANY_TYPE, TCP_ECHO_PORT);
    if (error) {
        sddf_printf("Failed to bind TCP echo socket: %s\n", lwip_strerr(error));
        return -1;
    }

    pcb = tcp_listen_with_backlog_and_err(pcb, 1, &error);
    if (error) {
        sddf_printf("Failed to listen on TCP echo socket: %s\n", lwip_strerr(error));
        return -1;
    }

    tcp_accept(pcb, tcp_echo_accept);

    return 0;
}
