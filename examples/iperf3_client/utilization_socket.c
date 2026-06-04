/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <os/sddf.h>

#include "lwip/ip.h"
#include "lwip/pbuf.h"
#include "lwip/tcp.h"

#include <sddf/benchmark/bench.h>
#include <sddf/benchmark/config.h>
#include <sddf/util/printf.h>

#include "iperf3_util.h"

/* Implements the ipbench TCP utilisation measurement protocol so that an
 * external ipbench client can measure CPU utilisation during an iperf3 test.
 *
 * Protocol:
 *   Server → "100 IPBENCH V1.0\n"
 *   Client → "HELLO\n"
 *   Server → "200 OK (Ready to go)\n"
 *   Client → "LOAD cpu_target_lukem\n"
 *   Server → "200 OK\n"
 *   Client → "SETUP args::\"\"\n"
 *   Server → "200 OK\n"
 *   Client → "START\n"   (snapshots cycle counters)
 *   Client → "STOP\n"    (reads counters, sends result, closes)
 *   Server → "220 VALID DATA (Data to follow)\nContent-length: N\n,idle,total"
 *
 * Only one client can be connected at a time.
 */

static struct tcp_pcb *utiliz_socket;

#define WHOAMI    "100 IPBENCH V1.0\n"
#define HELLO     "HELLO\n"
#define OK_READY  "200 OK (Ready to go)\n"
#define LOAD      "LOAD cpu_target_lukem\n"
#define OK        "200 OK\n"
#define SETUP     "SETUP args::\"\"\n"
#define START     "START\n"
#define STOP      "STOP\n"
#define QUIT      "QUIT\n"
#define ERROR     "400 ERROR\n"

#define msg_match(msg, match) (strncmp(msg, match, strlen(match)) == 0)

static benchmark_client_config_t *bench;

static uint64_t core_ccount_start[CONFIG_MAX_NUM_NODES];
static uint64_t idle_ccount_start[CONFIG_MAX_NUM_NODES];

#define MAX_TCP_DATA_LEN 1460
static char data_packet_str[MAX_TCP_DATA_LEN];

static inline void my_reverse(char s[])
{
    unsigned int i, j;
    char c;
    for (i = 0, j = strlen(s) - 1; i < j; i++, j--) {
        c = s[i]; s[i] = s[j]; s[j] = c;
    }
}

static inline void my_itoa(uint64_t n, char s[])
{
    unsigned int i = 0;
    do {
        s[i++] = n % 10 + '0';
    } while ((n /= 10) > 0);
    s[i] = '\0';
    my_reverse(s);
}

static err_t utilization_sent_callback(void *arg, struct tcp_pcb *pcb, u16_t len)
{
    return ERR_OK;
}

static err_t utilization_recv_callback(void *arg, struct tcp_pcb *pcb, struct pbuf *p, err_t err)
{
    if (p == NULL) {
        tcp_close(pcb);
        return ERR_OK;
    }

    pbuf_copy_partial(p, (void *)data_packet_str, p->tot_len, 0);
    err_t error;

    if (msg_match(data_packet_str, HELLO)) {
        error = tcp_write(pcb, OK_READY, strlen(OK_READY), TCP_WRITE_FLAG_COPY);
        if (error) sddf_dprintf("utilization: failed to send OK_READY\n");
    } else if (msg_match(data_packet_str, LOAD)) {
        error = tcp_write(pcb, OK, strlen(OK), TCP_WRITE_FLAG_COPY);
        if (error) sddf_dprintf("utilization: failed to send OK (LOAD)\n");
    } else if (msg_match(data_packet_str, SETUP)) {
        error = tcp_write(pcb, OK, strlen(OK), TCP_WRITE_FLAG_COPY);
        if (error) sddf_dprintf("utilization: failed to send OK (SETUP)\n");
    } else if (msg_match(data_packet_str, START)) {
        sddf_printf("utilization: measurement starting\n");
        if (bench->num_cores) {
            for (uint8_t i = 0; i < bench->num_cores; i++) {
                struct bench *b = (struct bench *)bench->core_ccounts[i];
                core_ccount_start[i] = __atomic_load_n(&b->core_ccount, __ATOMIC_RELAXED);
                idle_ccount_start[i] = __atomic_load_n(&b->idle_ccount, __ATOMIC_RELAXED);
            }
            microkit_notify(bench->start_ch);
        }
    } else if (msg_match(data_packet_str, STOP)) {
        sddf_printf("utilization: measurement finished\n");

        uint64_t total = 0, idle = 0;
        for (uint8_t i = 0; i < bench->num_cores; i++) {
            struct bench *b = (struct bench *)bench->core_ccounts[i];
            total += __atomic_load_n(&b->core_ccount, __ATOMIC_RELAXED) - core_ccount_start[i];
            idle  += __atomic_load_n(&b->idle_ccount, __ATOMIC_RELAXED) - idle_ccount_start[i];
        }

        char tbuf[21], ibuf[21], lbuf[16];
        my_itoa(total, tbuf);
        my_itoa(idle, ibuf);

        /* Message format: ",idle,total\0" — note ipbench expects idle first */
        int len = strlen(ibuf) + strlen(tbuf) + 3;
        my_itoa(len, lbuf);

        char buffer[120];
        strcat(strcpy(buffer, "220 VALID DATA (Data to follow)\nContent-length: "), lbuf);
        strcat(buffer, "\n,");
        strcat(buffer, ibuf);
        strcat(buffer, ",");
        strcat(buffer, tbuf);

        error = tcp_write(pcb, buffer, strlen(buffer) + 1, TCP_WRITE_FLAG_COPY);
        tcp_shutdown(pcb, 0, 1);

        if (bench->num_cores) {
            microkit_notify(bench->stop_ch);
        }

        if (total > 0) {
            sddf_printf("[cpu_util] %.1f%% (busy=%llu idle=%llu total=%llu cycles)\n",
                (double)(total - idle) / (double)total * 100.0,
                (unsigned long long)(total - idle),
                (unsigned long long)idle,
                (unsigned long long)total);
        } else {
            sddf_printf("[cpu_util] no data — build with MICROKIT_CONFIG=benchmark\n");
        }
    } else if (msg_match(data_packet_str, QUIT)) {
        /* nothing */
    } else {
        sddf_dprintf("utilization: unrecognised message: %s\n", data_packet_str);
        error = tcp_write(pcb, ERROR, strlen(ERROR), TCP_WRITE_FLAG_COPY);
        if (error) sddf_dprintf("utilization: failed to send ERROR\n");
    }

    return ERR_OK;
}

static err_t utilization_accept_callback(void *arg, struct tcp_pcb *newpcb, err_t err)
{
    sddf_printf("utilization: connection established\n");
    err_t error = tcp_write(newpcb, WHOAMI, strlen(WHOAMI), TCP_WRITE_FLAG_COPY);
    if (error) sddf_dprintf("utilization: failed to send WHOAMI\n");
    tcp_sent(newpcb, utilization_sent_callback);
    tcp_recv(newpcb, utilization_recv_callback);
    return ERR_OK;
}

int setup_utilization_socket(void *benchmark_config)
{
    bench = (benchmark_client_config_t *)benchmark_config;

    utiliz_socket = tcp_new_ip_type(IPADDR_TYPE_V4);
    if (utiliz_socket == NULL) {
        sddf_dprintf("utilization: failed to create socket\n");
        return -1;
    }

    err_t error = tcp_bind(utiliz_socket, IP_ANY_TYPE, UTILIZATION_PORT);
    if (error) {
        sddf_dprintf("utilization: failed to bind socket\n");
        return -1;
    }

    utiliz_socket = tcp_listen_with_backlog_and_err(utiliz_socket, 1, &error);
    if (error != ERR_OK) {
        sddf_dprintf("utilization: failed to listen on socket\n");
        return -1;
    }

    tcp_accept(utiliz_socket, utilization_accept_callback);
    return 0;
}
