/*
 * Copyright 2020, Data61, CSIRO
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <microkit.h>

#include "lwip/ip.h"
#include "lwip/pbuf.h"
#include "lwip/tcp.h"

#include <sddf/benchmark/bench.h>
#include <sddf/benchmark/config.h>
#include <sddf/util/printf.h>

#include "echo.h"

#define MAX_PACKET_SIZE 0x1000

/* This file implements a TCP based utilization measurment process that starts
 * and stops utilization measurements based on a client's requests.
 * The protocol used to communicate is as follows:
 * - Client connects
 * - Server sends: 100 IPBENCH V1.0\n
 * - Client sends: HELLO\n
 * - Server sends: 200 OK (Ready to go)\n
 * - Client sends: LOAD cpu_target_lukem\n
 * - Server sends: 200 OK\n
 * - Client sends: SETUP args::""\n
 * - Server sends: 200 OK\n
 * - Client sends: START\n
 * - Client sends: STOP\n
 * - Server sends: 220 VALID DATA (Data to follow)\n
 *                                Content-length: %d\n
 *                                ${content}\n
 * - Server closes socket.
 *
 * It is also possible for client to send QUIT\n during operation.
 *
 * The server starts recording utilization stats when it receives START and
 * finishes recording when it receives STOP.
 *
 * Only one client can be connected.
 */

static struct tcp_pcb *utiliz_socket;

#define WHOAMI "100 IPBENCH V1.0\n"
#define HELLO "HELLO\n"
#define OK_READY "200 OK (Ready to go)\n"
#define LOAD "LOAD cpu_target_lukem\n"
#define OK "200 OK\n"
#define SETUP "SETUP args::\"\"\n"
#define START "START\n"
#define STOP "STOP\n"
#define QUIT "QUIT\n"
#define RESPONSE "220 VALID DATA (Data to follow)\n"    \
    "Content-length: %d\n"                              \
    "%s\n"
#define IDLE_FORMAT ",%ld,%ld"
#define ERROR "400 ERROR\n"

#define msg_match(msg, match) (strncmp(msg, match, strlen(match))==0)

#define STR_HELPER(x) #x
#define STR(x) STR_HELPER(x)
#define RES(x, y, z) "220 VALID DATA (Data to follow)\n"    \
    "Content-length: "STR(x)"\n"\
    ","STR(y)","STR(z)

benchmark_client_config_t *bench;

uint64_t core_ccount_start[BENCHMARK_MAX_CORES];
uint64_t idle_ccount_start[BENCHMARK_MAX_CORES];

char data_packet_str[MAX_PACKET_SIZE];

static inline void my_reverse(char s[])
{
    unsigned int i, j;
    char c;

    for (i = 0, j = strlen(s)-1; i<j; i++, j--) {
        c = s[i];
        s[i] = s[j];
        s[j] = c;
    }
}

static inline void my_itoa(uint64_t n, char s[])
{
    unsigned int i;
    uint64_t sign;

    if ((sign = n) < 0)  /* record sign */
        n = -n;          /* make n positive */
    i = 0;
    do {       /* generate digits in reverse order */
        s[i++] = n % 10 + '0';   /* get next digit */
    } while ((n /= 10) > 0);     /* delete it */
    if (sign < 0)
        s[i++] = '-';
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
        if (error) sddf_dprintf("Failed to send OK_READY message through utilization peer\n");
    } else if (msg_match(data_packet_str, LOAD)) {
        error = tcp_write(pcb, OK, strlen(OK), TCP_WRITE_FLAG_COPY);
        if (error) sddf_dprintf("Failed to send OK message through utilization peer\n");
    } else if (msg_match(data_packet_str, SETUP)) {
        error = tcp_write(pcb, OK, strlen(OK), TCP_WRITE_FLAG_COPY);
        if (error) sddf_dprintf("Failed to send OK message through utilization peer\n");
    } else if (msg_match(data_packet_str, START)) {
        sddf_printf("%s measurement starting...\n", microkit_name);
        for (uint8_t i = 0; i < bench->num_cores; i++) {
            struct bench *ccounts = (struct bench *)bench->core_ccounts[i];
            core_ccount_start[i] = __atomic_load_n(&ccounts->ts, __ATOMIC_RELAXED);
            idle_ccount_start[i] = __atomic_load_n(&ccounts->ccount, __ATOMIC_RELAXED);
            if (i == bench->num_cores - 1) {
                microkit_notify(bench->start_ch);
            }
        }
    } else if (msg_match(data_packet_str, STOP)) {
        sddf_printf("%s measurement finished \n", microkit_name);

        uint64_t total = 0, idle = 0;
        for (uint8_t i = 0; i < bench->num_cores; i++) {
            struct bench *ccounts = (struct bench *)bench->core_ccounts[i];
            total += __atomic_load_n(&ccounts->ts, __ATOMIC_RELAXED) - core_ccount_start[i];
            idle += __atomic_load_n(&ccounts->ccount, __ATOMIC_RELAXED) - idle_ccount_start[i];
        }

        char tbuf[21];
        my_itoa(total, tbuf);

        char ibuf[21];
        my_itoa(idle, ibuf);

        /* Message format: ",total,idle\0" */
        int len = strlen(tbuf) + strlen(ibuf) + 3;
        char lbuf[16];
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
    } else if (msg_match(data_packet_str, QUIT)) {
        /* Do nothing for now */
    } else {
        sddf_dprintf("Received a message that we can't handle %s\n", data_packet_str);
        error = tcp_write(pcb, ERROR, strlen(ERROR), TCP_WRITE_FLAG_COPY);
        if (error) sddf_dprintf("Failed to send OK message through utilization peer\n");
    }

    return ERR_OK;
}

static err_t utilization_accept_callback(void *arg, struct tcp_pcb *newpcb, err_t err)
{
    sddf_printf("Utilization connection established!\n");
    err_t error = tcp_write(newpcb, WHOAMI, strlen(WHOAMI), TCP_WRITE_FLAG_COPY);
    if (error) sddf_dprintf("Failed to send WHOAMI message through utilization peer\n");
    tcp_sent(newpcb, utilization_sent_callback);
    tcp_recv(newpcb, utilization_recv_callback);

    return ERR_OK;
}

int setup_utilization_socket(void *benchmark_config)
{
    bench = (benchmark_client_config_t *)benchmark_config;

    utiliz_socket = tcp_new_ip_type(IPADDR_TYPE_V4);
    if (utiliz_socket == NULL) {
        sddf_dprintf("Failed to open a socket for listening!\n");
        return -1;
    }

    err_t error = tcp_bind(utiliz_socket, IP_ANY_TYPE, UTILIZATION_PORT);
    if (error) {
        sddf_dprintf("Failed to bind the TCP socket");
        return -1;
    }

    utiliz_socket = tcp_listen_with_backlog_and_err(utiliz_socket, 1, &error);
    if (error != ERR_OK) {
        sddf_dprintf("Failed to listen on the utilization socket\n");
        return -1;
    }
    tcp_accept(utiliz_socket, utilization_accept_callback);

    return 0;
}
