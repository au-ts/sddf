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
#include <sddf/network/vswitch.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/benchmark/config.h>
#include "lwip/ip4_addr.h"
#include "lwip/pbuf.h"

#include "icmp.h"

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

__attribute__((__section__(".net_client_config"))) net_client_config_t net_config;

__attribute__((__section__(".lib_sddf_lwip_config"))) lib_sddf_lwip_config_t lib_sddf_lwip_config;

serial_queue_handle_t serial_tx_queue_handle;

net_queue_handle_t net_rx_handle;
net_queue_handle_t net_tx_handle;

typedef struct neighbors {
    bool pingable;
    icmp_context_t icmp_ctx;
} neighbors_t;

static neighbors_t neighbors[SDDF_NET_MAX_CLIENTS];

#define LWIP_TICK_MS 100

/**
 * Pings all other reachable vswitch clients exactly once, after their IP
 * address has been discovered.
 */
static void ping_neighbors()
{
    for (uint8_t i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        if (!neighbors[i].pingable || !neighbors[i].icmp_ctx.ip_addr || neighbors[i].icmp_ctx.pinged) {
            continue;
        }
        send_icmp_request(&neighbors[i].icmp_ctx, i);
        neighbors[i].icmp_ctx.pinged = true;
    }
}

/**
 * Request IP address of all reachable neighbours using PPC to the vswitch.
 */
static void query_ips()
{
    for (uint8_t i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        if (!neighbors[i].pingable || neighbors[i].icmp_ctx.ip_addr) {
            continue;
        }

        sddf_set_mr(VSWITCH_REQ_CLIENT_ID, i);
        sddf_ppcall(net_config.tx.id, seL4_MessageInfo_new(VSWITCH_REQ_CLIENT, 0, 0, VSWITCH_REQ_NUM_ARGS));
        vswitch_err_t err = sddf_get_mr(VSWITCH_REQ_RET_ERR);
        if (err == VSWITCH_ERR_VIRT_PORT) {
            neighbors[i].pingable = false;
            continue;
        } else if (err != VSWITCH_ERR_OKAY) {
            continue;
        }

        neighbors[i].icmp_ctx.ip_addr = sddf_get_mr(VSWITCH_REQ_RET_IP_ADDR);
    }
}

/**
 * Netif status callback function that outputs client's name and the obtained IP address.
 * Reports the IP address to vswitch.
 *
 * @param ip_addr ip address of the client.
 */
void netif_status_callback(char *ip_addr)
{
    sddf_printf("DHCP request finished, IP address for netif %s is: %s\n", sddf_get_pd_name(), ip_addr);
    ip4_addr_t temp;
    ipaddr_aton(ip_addr, &temp);
    uint32_t ip = ip4_addr_get_u32(&temp);
    sddf_set_mr(VSWITCH_SET_IP_ADDR_ARG, ip);
    sddf_ppcall(net_config.tx.id, seL4_MessageInfo_new(VSWITCH_SET_IP_ADDR, 0, 0, VSWITCH_SET_NUM_ARGS));
    vswitch_err_t err = sddf_get_mr(VSWITCH_SET_RET_ERR);
    if (err != VSWITCH_ERR_OKAY) {
        sddf_printf("Client %s could not register IP address with vswitch!\n", sddf_get_pd_name());
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
    icmp_init_raw();

    sddf_lwip_maybe_notify();

    /**
     * Discover your reachable vswitch neighbours.
     */
    sddf_ppcall(net_config.tx.id, seL4_MessageInfo_new(VSWITCH_QUERY_STATE, 0, 0, VSWITCH_QUERY_NUM_ARGS));
    vswitch_err_t err = sddf_get_mr(VSWITCH_QUERY_RET_ERR);
    if (err != VSWITCH_ERR_OKAY) {
        sddf_printf("Client %s could not query vswitch state!\n", sddf_get_pd_name());
    }

    uint64_t reachable_neighbours = sddf_get_mr(VSWITCH_QUERY_RET_REACHABLE_BITMAP);
    for (uint8_t i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        neighbors[i].pingable = reachable_neighbours & ((uint64_t)1 << i);
    }
}

static uint8_t tick_count = 0;

void notified(sddf_channel ch)
{
    if (ch == net_config.rx.id) {
        sddf_lwip_process_rx();
    } else if (ch == timer_config.driver_id) {
        sddf_lwip_process_timeout();
        set_timeout();
        tick_count++;
        if (tick_count == 50) {
            query_ips();
            ping_neighbors();
            tick_count = 0;
        }
    } else if (ch == serial_config.tx.id || ch == net_config.tx.id) {
        // Nothing to do
    } else {
        sddf_dprintf("LWIP|LOG: received notification on unexpected channel: %u\n", ch);
    }

    sddf_lwip_maybe_notify();
}

