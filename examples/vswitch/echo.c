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
#include <sddf/network/util.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/benchmark/config.h>
#include "lwip/pbuf.h"

#include "echo.h"

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

__attribute__((__section__(".net_client_config"))) net_client_config_t net_config;

__attribute__((__section__(".benchmark_client_config"))) benchmark_client_config_t benchmark_config;

__attribute__((__section__(".lib_sddf_lwip_config"))) lib_sddf_lwip_config_t lib_sddf_lwip_config;

__attribute__((__section__(".client_config"))) vswitch_client_config_t client_config;

serial_queue_handle_t serial_tx_queue_handle;

net_queue_handle_t net_rx_handle;
net_queue_handle_t net_tx_handle;

static uint32_t ip_addrs[SDDF_NET_MAX_CLIENTS];

#define LWIP_TICK_MS 100

// Add PPC that fires just after the DHCP has finished
// Save that into an array of IPs from neighbors, then we can ping each other and ensure that vswitch works
static void query_ips()
{
    sddf_ppcall(client_config.channel_id, seL4_MessageInfo_new(VSWITCH_QUERY_IP_ADDR, 0, 0, 0));
    uint8_t num_clients = sddf_get_mr(0), client_id = 0; // TODO: somehow this is wrong!? it gets 0 num clients, ask tomorrow
    uint32_t ipaddr = 0;
    sddf_dprintf("ECHO|LOG: received IP from vswitch num_clients: %d\n", num_clients);
    for (int i = 0; i < num_clients; i++) {
        client_id = sddf_get_mr(1 + 2 * i);
        ipaddr = sddf_get_mr(1 + 2 * i + 1);
        ip_addrs[client_id] = ipaddr;
        sddf_dprintf("ECHO|LOG: received IP from vswitch client_id: %d IP: 0x%x\n", client_id, ipaddr);
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
    // TODO: Here we PPC to vswitch, it then replies with the map of client_id and IPs that we can call into later
    uint32_t ip = sddf_lwip_ipaddr_aton(ip_addr);
    sddf_set_mr(0, ip);
    sddf_ppcall(client_config.channel_id, seL4_MessageInfo_new(VSWITCH_REPORT_IP_ADDR, 0, 0, 1));
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

    setup_udp_socket();
    setup_utilization_socket(&benchmark_config);
    setup_tcp_socket();

    sddf_lwip_maybe_notify();
}

static uint8_t cnt = 0;

void notified(sddf_channel ch)
{
    if (ch == net_config.rx.id) {
        sddf_lwip_process_rx();
    } else if (ch == timer_config.driver_id) {
        sddf_lwip_process_timeout();
        set_timeout();
        // Throttle it a bit - hacky
        cnt++;
        if (cnt == 100) {
            query_ips();
            cnt = 0;
        }
    } else if (ch == serial_config.tx.id || ch == net_config.tx.id) {
        // Nothing to do
    } else {
        sddf_dprintf("LWIP|LOG: received notification on unexpected channel: %u\n", ch);
    }

    sddf_lwip_maybe_notify();
}

