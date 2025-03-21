/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/util/util.h>
#include <sddf/util/string.h>
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

#include "echo.h"

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

__attribute__((__section__(".net_client_config"))) net_client_config_t net_config;

__attribute__((__section__(".benchmark_client_config"))) benchmark_client_config_t benchmark_config;

__attribute__((__section__(".lib_sddf_lwip_config"))) lib_sddf_lwip_config_t lib_sddf_lwip_config;

serial_queue_handle_t serial_tx_queue_handle;

net_queue_handle_t net_rx_handle;
net_queue_handle_t net_tx_handle;

#define LWIP_TICK_MS 100

struct pbuf *head;
struct pbuf *tail;

/**
 * Netif status callback function that output's client's name and
 * obtained IP address.
 *
 * @param ip_addr ip address of the client.
 */
void netif_status_callback(char *ip_addr)
{
    sddf_printf("DHCP request finished, IP address for netif %s is: %s\n", sddf_get_pd_name(), ip_addr);
}

/**
 * Sets a timeout for the next lwip tick.
 */
void set_timeout(void)
{
    sddf_timer_set_timeout(timer_config.driver_id, LWIP_TICK_MS * NS_IN_MS);
}

/**
 * Stores a pbuf to be transmitted upon available transmit buffers.
 *
 * @param p pbuf to be stored.
 */
net_sddf_err_t enqueue_pbufs(struct pbuf *p)
{
    /* Indicate to the tx virt that we wish to be notified about free tx buffers */
    net_request_signal_free(&net_tx_handle);

    if (head == NULL) {
        head = p;
    } else {
        tail->next_chain = p;
    }
    tail = p;

    /* Increment reference count to ensure this pbuf is not freed by lwip */
    pbuf_ref(p);

    return SDDF_LWIP_ERR_OK;
}

void transmit(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (head != NULL && !net_queue_empty_free(&net_tx_handle)) {
            net_sddf_err_t err = sddf_lwip_transmit_pbuf(head);
            if (err == SDDF_LWIP_ERR_PBUF) {
                sddf_dprintf("LWIP|ERROR: attempted to send a packet of size %u > BUFFER SIZE %u\n", head->tot_len,
                             NET_BUFFER_SIZE);
            } else if (err != SDDF_LWIP_ERR_OK) {
                sddf_dprintf("LWIP|ERROR: unkown error when trying to send pbuf %p\n", head);
            }

            struct pbuf *temp = head;
            head = temp->next_chain;
            if (head == NULL) {
                tail = NULL;
            }
            pbuf_free(temp);
        }

        /* Only request a signal if there are more pending pbufs to send */
        if (head == NULL || !net_queue_empty_free(&net_tx_handle)) {
            net_cancel_signal_free(&net_tx_handle);
        } else {
            net_request_signal_free(&net_tx_handle);
        }
        reprocess = false;

        if (head != NULL && !net_queue_empty_free(&net_tx_handle)) {
            net_cancel_signal_free(&net_tx_handle);
            reprocess = true;
        }
    }
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

    sddf_lwip_init(&lib_sddf_lwip_config, &net_config, &timer_config, net_rx_handle, net_tx_handle, NULL,
                   netif_status_callback, enqueue_pbufs);
    set_timeout();

    setup_udp_socket();
    setup_utilization_socket(benchmark_config.cycle_counters, benchmark_config.start_ch, benchmark_config.stop_ch);
    setup_tcp_socket();

    sddf_lwip_maybe_notify();
}

void notified(sddf_channel ch)
{
    if (ch == net_config.rx.id) {
        sddf_lwip_process_rx();
    } else if (ch == net_config.tx.id) {
        transmit();
    } else if (ch == timer_config.driver_id) {
        sddf_lwip_process_timeout();
        set_timeout();
    } else if (ch == serial_config.tx.id) {
        // Nothing to do
    } else {
        sddf_dprintf("LWIP|LOG: received notification on unexpected channel: %u\n", ch);
    }

    sddf_lwip_maybe_notify();
}
