/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/util/util.h>
#include <string.h>
#include <sddf/util/printf.h>
#include <sddf/network/lib_sddf_lwip.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/benchmark/config.h>
#include "lwip/pbuf.h"
#include "lwip/ip_addr.h"
#define IPERF_MAX_CONNS 1

// #include "iperf3_client.h"
#include "iperf3_ctrl.h"

static bool iperf3_started = false;

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

__attribute__((__section__(".net_client_config"))) net_client_config_t net_config;

__attribute__((__section__(".lib_sddf_lwip_config"))) lib_sddf_lwip_config_t lib_sddf_lwip_config;

__attribute__((__section__(".benchmark_client_config"))) benchmark_client_config_t benchmark_config;



serial_queue_handle_t serial_tx_queue_handle;

net_queue_handle_t net_rx_handle;
net_queue_handle_t net_tx_handle;

static iperf_ctrl_t ctrl;

#define LWIP_TICK_MS 100

static uint32_t prng_state = 0x12345678;

void prng_seed(uint32_t seed) {
    prng_state = seed ? seed : 0x12345678;
}

static uint32_t prng_next(void) {
    prng_state = prng_state * 1103515245u + 12345u;
    return prng_state;
}

void make_cookie(uint8_t *cookie) {
    static const char chars[] =
        "abcdefghijklmnopqrstuvwxyz0123456789";

    for (int i = 0; i < IPERF3_COOKIE_LEN; i++) {
        cookie[i] = chars[prng_next() % (sizeof(chars) - 1)];
    }
}

/**
 * Netif status callback function that output's client's name and
 * obtained IP address.
 *
 * @param ip_addr ip address of the client.
 */
void netif_status_callback(char *ip_addr)
{
    sddf_printf("DHCP request finished, IP address for netif %s is: %s\n", sddf_get_pd_name(), ip_addr);
    if (!iperf3_started) {
        iperf3_started = true;
        sddf_printf("Starting iperf3 now (DHCP ready)\n");
        ip_addr_t server_addr;
        IP_ADDR4(&server_addr, 172, 16, 0, 101);
        struct tcp_pcb *pcb;

        pcb = tcp_new_ip_type(IPADDR_TYPE_V4);
        if (pcb == NULL) {
            sddf_printf("iperf3_client: failed to create PCB\n");
            return;
        }
        err_t error = tcp_bind(pcb, IP_ANY_TYPE, 0);
        if (error) {
            sddf_printf("Failed to bind TCP  socket: %s\n", lwip_strerr(error));
            return;
        }


        iperf3_ctrl_init(&ctrl);

        tcp_arg(pcb, &ctrl);
        uint32_t seed = 0;
        char *name = sddf_get_pd_name();

        while (*name) {
            seed = seed * 33 + *name;
            name++;
        }

        prng_seed(seed);

        make_cookie(ctrl.cookie);
        uint16_t port = (!strcmp(ip_addr, "172.16.2.253")) ? 5202 : 5203;
        ctrl.server_port = port;
        ctrl.server_addr = server_addr;

        sddf_printf("[%s] ctrl local port = %u\n", sddf_get_pd_name(), pcb->local_port);
        sddf_printf("[%s] cookie = %.37s\n", sddf_get_pd_name(), ctrl.cookie);
        error = tcp_connect(pcb, &ctrl.server_addr, ctrl.server_port, iperf_ctrl_connect);
        if (error) {
            sddf_printf("Failed to connect to TCP  socket: %s\n", lwip_strerr(error));
            return;
        }
    }
}

/**
 * Sets a timeout for the next lwip tick.
 */
void set_timeout(void)
{
    sddf_timer_set_timeout(timer_config.driver_id, LWIP_TICK_MS * NS_IN_MS);
}

void init(void)
{   
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);
    net_queue_init(&net_rx_handle, net_config.rx.free_queue.vaddr, net_config.rx.active_queue.vaddr,
                   net_config.rx.num_buffers);
    net_queue_init(&net_tx_handle, net_config.tx.free_queue.vaddr, net_config.tx.active_queue.vaddr,
                   net_config.tx.num_buffers);
    net_buffers_init(&net_tx_handle, 0);

    sddf_lwip_init(&lib_sddf_lwip_config, &net_config, &timer_config, net_rx_handle, net_tx_handle, NULL, NULL,
                   netif_status_callback, NULL, NULL, NULL);
    set_timeout();

    sddf_lwip_maybe_notify();
}

void notified(sddf_channel ch)
{
    if (ch == net_config.rx.id) {
        sddf_lwip_process_rx();
    } else if (ch == timer_config.driver_id) {

        sddf_lwip_process_timeout();
        set_timeout();
    } else if (ch == serial_config.tx.id || ch == net_config.tx.id) {
        // Nothing to do
    } else {
        sddf_dprintf("LWIP|LOG: received notification on unexpected channel: %u\n", ch);
    }

    sddf_lwip_maybe_notify();
}