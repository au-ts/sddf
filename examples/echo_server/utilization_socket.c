/*
 * Copyright 2020, Data61, CSIRO
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <string.h>
#include <microkit.h>
#include <sel4/benchmark_utilisation_types.h>

#include "lwip/ip.h"
#include "lwip/pbuf.h"
#include "lwip/tcp.h"

#include <sddf/util/util.h>
#include <sddf/benchmark/bench.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>

#include "echo.h"

#define TIMER  1
#define START_PMU 4
#define STOP_PMU 5
#define STOP_COUNTER 9

#define MAX_PACKET_SIZE 0x1000

uintptr_t cyclecounters_vaddr = 0x5010000;

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


struct bench *bench;

uint64_t start;
uint64_t idle_ccount_start;

uint64_t eth_pcount_tx_start;
uint64_t eth_pcount_rx_start;
uint64_t eth_rx_irq_count_start;
uint64_t eth_irq_count_start;
uint64_t eth_rx_notified_start;
uint64_t eth_idle_rx_notified_start;
uint64_t eth_tx_notified_start;
uint64_t eth_idle_tx_notified_start;
uint64_t eth_rx_notify_start;
uint64_t eth_request_signal_rx_start;
uint64_t eth_rx_free_capacity_start;
uint64_t virt_rx_notify_start;
uint64_t lwip_rx_notified_start;
uint64_t lwip_tx_notified_start;
uint64_t lwip_rx_notify_start;
uint64_t lwip_tx_notify_start;

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
        uint64_t now = sddf_timer_time_now(TIMER);
        sddf_printf("%s measurement starting at %lu ... \n", "client0", now);
        if (!strcmp("client0", "client0")) {
            start = __atomic_load_n(&bench->ts, __ATOMIC_RELAXED);
            idle_ccount_start = __atomic_load_n(&bench->ccount, __ATOMIC_RELAXED);
            eth_pcount_tx_start = __atomic_load_n(&bench->eth_pcount_tx, __ATOMIC_RELAXED);
            eth_pcount_rx_start = __atomic_load_n(&bench->eth_pcount_rx, __ATOMIC_RELAXED);
            eth_rx_irq_count_start = __atomic_load_n(&bench->eth_rx_irq_count, __ATOMIC_RELAXED);
            eth_irq_count_start = __atomic_load_n(&bench->eth_irq_count, __ATOMIC_RELAXED);
            eth_rx_notified_start = __atomic_load_n(&bench->eth_rx_notified, __ATOMIC_RELAXED);
            eth_idle_rx_notified_start = __atomic_load_n(&bench->eth_idle_rx_notified, __ATOMIC_RELAXED);
            eth_tx_notified_start = __atomic_load_n(&bench->eth_tx_notified, __ATOMIC_RELAXED);
            eth_idle_tx_notified_start = __atomic_load_n(&bench->eth_idle_tx_notified, __ATOMIC_RELAXED);
            eth_rx_notify_start = __atomic_load_n(&bench->eth_rx_notify, __ATOMIC_RELAXED);
            eth_request_signal_rx_start = __atomic_load_n(&bench->eth_request_signal_rx, __ATOMIC_RELAXED);
            eth_rx_free_capacity_start = __atomic_load_n(&bench->eth_rx_free_capacity, __ATOMIC_RELAXED);
            virt_rx_notify_start = __atomic_load_n(&bench->virt_rx_notify, __ATOMIC_RELAXED);
            lwip_rx_notified_start = __atomic_load_n(&bench->lwip_rx_notified, __ATOMIC_RELAXED);
            lwip_tx_notified_start = __atomic_load_n(&bench->lwip_tx_notified, __ATOMIC_RELAXED);
            lwip_rx_notify_start = __atomic_load_n(&bench->lwip_rx_notify, __ATOMIC_RELAXED);
            lwip_tx_notify_start = __atomic_load_n(&bench->lwip_tx_notify, __ATOMIC_RELAXED);

            __atomic_store_n(&bench->eth_rx_free_min_capacity, 512, __ATOMIC_RELAXED);
            __atomic_store_n(&bench->eth_rx_free_max_capacity, 0, __ATOMIC_RELAXED);

            microkit_notify(START_PMU);
        }
    } else if (msg_match(data_packet_str, STOP)) {
        if (!strcmp("client0", "client0")) {
            microkit_notify(STOP_PMU);
            microkit_notify(STOP_COUNTER);
        }
        uint64_t now = sddf_timer_time_now(TIMER);
        sddf_printf("%s measurement finished at: %lu\n", "client0", now);

        uint64_t total = 0, idle = 0;

        if (!strcmp("client0", "client0")) {
            total = __atomic_load_n(&bench->ts, __ATOMIC_RELAXED) - start;
            idle = __atomic_load_n(&bench->ccount, __ATOMIC_RELAXED) - idle_ccount_start;
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

        if (!strcmp("client0", "client0")) {
            uint64_t eth_pcount_tx = __atomic_load_n(&bench->eth_pcount_tx, __ATOMIC_RELAXED) - eth_pcount_tx_start;
            uint64_t eth_pcount_rx = __atomic_load_n(&bench->eth_pcount_rx, __ATOMIC_RELAXED) - eth_pcount_rx_start;
            uint64_t eth_rx_irq_count = __atomic_load_n(&bench->eth_rx_irq_count, __ATOMIC_RELAXED) - eth_rx_irq_count_start;
            uint64_t eth_irq_count = __atomic_load_n(&bench->eth_irq_count, __ATOMIC_RELAXED) - eth_irq_count_start;
            uint64_t eth_rx_notified = __atomic_load_n(&bench->eth_rx_notified, __ATOMIC_RELAXED) - eth_rx_notified_start;
            uint64_t eth_idle_rx_notified = __atomic_load_n(&bench->eth_idle_rx_notified, __ATOMIC_RELAXED) - eth_idle_rx_notified_start;
            uint64_t eth_tx_notified = __atomic_load_n(&bench->eth_tx_notified, __ATOMIC_RELAXED) - eth_tx_notified_start;
            uint64_t eth_idle_tx_notified = __atomic_load_n(&bench->eth_idle_tx_notified, __ATOMIC_RELAXED) - eth_idle_tx_notified_start;
            uint64_t eth_rx_notify = __atomic_load_n(&bench->eth_rx_notify, __ATOMIC_RELAXED) - eth_rx_notify_start;
            uint64_t eth_request_signal_rx = __atomic_load_n(&bench->eth_request_signal_rx, __ATOMIC_RELAXED) - eth_request_signal_rx_start;
            uint64_t eth_rx_free_capacity = __atomic_load_n(&bench->eth_rx_free_capacity, __ATOMIC_RELAXED) - eth_rx_free_capacity_start;
            uint64_t eth_rx_free_min_capacity = __atomic_load_n(&bench->eth_rx_free_min_capacity, __ATOMIC_RELAXED);
            uint64_t eth_rx_free_max_capacity = __atomic_load_n(&bench->eth_rx_free_max_capacity, __ATOMIC_RELAXED);
        
            uint64_t virt_rx_notify = __atomic_load_n(&bench->virt_rx_notify, __ATOMIC_RELAXED) - virt_rx_notify_start;
            uint64_t lwip_rx_notified = __atomic_load_n(&bench->lwip_rx_notified, __ATOMIC_RELAXED) - lwip_rx_notified_start;
            uint64_t lwip_tx_notified = __atomic_load_n(&bench->lwip_tx_notified, __ATOMIC_RELAXED) - lwip_tx_notified_start;
            uint64_t lwip_rx_notify = __atomic_load_n(&bench->lwip_rx_notify, __ATOMIC_RELAXED) - lwip_rx_notify_start;
            uint64_t lwip_tx_notify = __atomic_load_n(&bench->lwip_tx_notify, __ATOMIC_RELAXED) - lwip_tx_notify_start;

            uint64_t avg_capacity;
            if (eth_rx_notified) {
                avg_capacity = eth_rx_free_capacity / eth_rx_notified;
            } else {
                avg_capacity = 0;
            }

            sddf_printf("NIC RX pk,NIC RX dropped pk,driver RX pk,driver TX pk,driver RX IRQ,driver IRQ,");
            sddf_printf("driver RX notified,driver RX idle notified,driver TX notified,driver TX idle notified,driver RX notify,driver RX Request,");
            sddf_printf("driver rx free avg buf,driver rx free min buf,driver rx free max buf,");
            sddf_printf("virt rx notified, lwip rx notified, lwip tx notified, lwip rx notify, lwip tx notify\n");

            sddf_printf("%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,%ld,\n",
                        bench->hw_pcount_rx, bench->hw_pcount_rx_dropped,
                        eth_pcount_tx, eth_pcount_rx,
                        eth_rx_irq_count, eth_irq_count,
                        eth_rx_notified, eth_idle_rx_notified, eth_tx_notified, eth_idle_tx_notified,
                        eth_rx_notify, eth_request_signal_rx,
                        avg_capacity, eth_rx_free_min_capacity, eth_rx_free_max_capacity, 
                        virt_rx_notify, lwip_rx_notified, lwip_tx_notified, 
                        lwip_rx_notify, lwip_tx_notify);
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

int setup_utilization_socket(void)
{
    bench = (void *)cyclecounters_vaddr;
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
