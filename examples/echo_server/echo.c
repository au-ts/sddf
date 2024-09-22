/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/string.h>
#include <sddf/util/printf.h>
#include <sddf/network/lib_sddf_lwip.h>
#include <sddf/network/queue.h>
#include <sddf/serial/queue.h>
#include <sddf/timer/client.h>
#include <sddf/benchmark/sel4bench.h>
#include <serial_config.h>
#include <ethernet_config.h>
#include "lwip/pbuf.h"

#include "echo.h"

#define SERIAL_TX_CH 0
#define TIMER_CH  1
#define RX_CH  2
#define TX_CH  3

char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;

net_queue_t *rx_free;
net_queue_t *rx_active;
net_queue_t *tx_free;
net_queue_t *tx_active;
uintptr_t rx_buffer_data_region;
uintptr_t tx_buffer_data_region;

net_queue_handle_t net_rx_handle;
net_queue_handle_t net_tx_handle;

#define LWIP_TICK_MS 100

struct pbuf *head;
struct pbuf *tail;

/**
 * Netif status callback function that output's client's Microkit name and
 * obtained IP address.
 *
 * @param ip_addr ip address of the client.
 */
void netif_status_callback(char *ip_addr)
{
    sddf_printf("DHCP request finished, IP address for netif %s is: %s\n", microkit_name, ip_addr);
}

/**
 * Sets a timeout for the next lwip tick.
 */
void set_timeout(void)
{
    sddf_timer_set_timeout(TIMER_CH, LWIP_TICK_MS * NS_IN_MS);
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
    serial_cli_queue_init_sys(microkit_name, NULL, NULL, NULL, &serial_tx_queue_handle, serial_tx_queue,
                              serial_tx_data);
    serial_putchar_init(SERIAL_TX_CH, &serial_tx_queue_handle);

    size_t rx_size, tx_size;
    net_cli_queue_size(microkit_name, &rx_size, &tx_size);
    net_queue_init(&net_rx_handle, rx_free, rx_active, rx_size);
    net_queue_init(&net_tx_handle, tx_free, tx_active, tx_size);
    net_buffers_init(&net_tx_handle, 0);

    sddf_lwip_init(net_rx_handle, net_tx_handle, RX_CH, TX_CH, rx_buffer_data_region, tx_buffer_data_region, TIMER_CH,
                   net_cli_mac_addr(microkit_name), NULL, netif_status_callback, enqueue_pbufs);
    set_timeout();

    setup_udp_socket();
    setup_utilization_socket();
    setup_tcp_socket();

    sddf_lwip_maybe_notify();
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case RX_CH:
        sddf_lwip_process_rx();
        break;
    case TIMER_CH:
        sddf_lwip_process_timeout();
        set_timeout();
        break;
    case TX_CH:
        transmit();
        break;
    case SERIAL_TX_CH:
        break;
    default:
        sddf_dprintf("LWIP|LOG: received notification on unexpected channel: %u\n", ch);
        break;
    }

    sddf_lwip_maybe_notify();
}
