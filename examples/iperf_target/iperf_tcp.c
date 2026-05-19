/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <os/sddf.h>

// #include "echo.h"
#include "lwip/ip.h"
#include "lwip/pbuf.h"
#include "lwip/tcp.h"

#include <sddf/util/util.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>

#include "iperf.h"
// #define IPERF_MAX_CONNS 4
// #define IPERF_PORT 5201

extern timer_client_config_t timer_config;

struct iperf_conn {
    bool in_use;
    bool reverse;
    uint64_t bytes_rx;
    uint64_t bytes_tx;
    uint64_t start_ns;
    uint64_t last_report_ns;
    uint64_t duration_s;
    uint32_t target_rate_bps;
};

static struct iperf_conn tcp_state_pool[IPERF_MAX_CONNS];
/*
 * Allocate a new TCP state structure.
 */
static struct iperf_conn *tcp_state_alloc()
{
    for (int i = 0; i < IPERF_MAX_CONNS; ++i) {
        if (!tcp_state_pool[i].in_use) {
            tcp_state_pool[i].in_use = true;
            return &tcp_state_pool[i];
        }
    }
    return NULL;
}

/*
 * Free a TCP state structure.
 */
static void tcp_state_free(struct iperf_conn *state)
{
    assert(state);
    assert(state->in_use);
    state->in_use = false;
}

/*
 * Callback invoked to update TCP state when data has been received. First
 * checks if there is free space available to store the data in the TCP state
 * buffer. Next copies the data into the buffer. Finally attempts to re-transmit
 * the data back to the source.
 */
static err_t iperf_tcp_recv(void *arg, struct tcp_pcb *pcb, struct pbuf *p, err_t err)
{
    struct iperf_conn *state = arg;
    assert(state != NULL);

    if (p == NULL) {
        /* Closing. */
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

    state->bytes_rx += p->tot_len;

    tcp_recved(pcb, p->tot_len);

    pbuf_free(p);
    return ERR_OK;
}

/*
 * Prints an LWIP TCP error and and frees the erroneous TCP state structure.
 */
static void iperf_tcp_err(void *arg, err_t err)
{
    struct iperf_conn *state = arg;
    assert(state != NULL);

    sddf_printf("tcp_echo: %s\n", lwip_strerr(err));

    tcp_state_free(state);
}

/*
 * Accepts a new TCP echo socket connection and allocates and initialises a TCP
 * state structure.
 */
static err_t iperf_tcp_accept(void *arg, struct tcp_pcb *pcb, err_t err)
{
    struct iperf_conn *state = tcp_state_alloc();
    if (state == NULL) {
        sddf_printf("tcp_echo: failed to alloc state\n");
        return ERR_MEM;
    }

    sddf_printf("tcp_echo[%s:%d]: accept\n",
                ipaddr_ntoa(&pcb->remote_ip), pcb->remote_port
               );

    state->reverse = false;
    state->bytes_rx = 0;
    state->bytes_tx = 0;
    state->start_ns = sddf_timer_time_now(timer_config.driver_id);
    state->last_report_ns = state->start_ns;

    tcp_nagle_disable(pcb);
    tcp_arg(pcb, state);
    tcp_recv(pcb, iperf_tcp_recv);
    tcp_err(pcb, iperf_tcp_err);

    return ERR_OK;
}

/*
 * Intitialise an LWIP TCP echo socket and register relevant callback functions.
*/
int iperf_tcp_init(void)
{
    struct tcp_pcb *pcb;

    pcb = tcp_new_ip_type(IPADDR_TYPE_V4);
    if (pcb == NULL) {
        sddf_printf("Failed to open TCP echo socket\n");
        return -1;
    }

    err_t error = tcp_bind(pcb, IP_ANY_TYPE, IPERF_PORT);
    if (error) {
        sddf_printf("Failed to bind TCP echo socket: %s\n", lwip_strerr(error));
        return -1;
    }

    pcb = tcp_listen_with_backlog_and_err(pcb, 1, &error);
    if (error) {
        sddf_printf("Failed to listen on TCP echo socket: %s\n", lwip_strerr(error));
        return -1;
    }

    tcp_accept(pcb, iperf_tcp_accept);

    return 0;
}
