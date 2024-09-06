/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>
#include <sddf/network/queue.h>
#include "lwip/pbuf.h"

/* Default gigabit link speed. */
#define SDDF_LWIP_LINK_SPEED 1000000000

/* Default ethernet MTU. */
#define SDDF_LWIP_ETHER_MTU 1500

/* Definitions for sDDF error constants. */
typedef enum {
    /* No error, everything OK. */
    SDDF_ERR_OK = 0,
    /* Pbuf too large for sDDF buffer. */
    SDDF_ERR_PBUF = -1,
    /* No buffers available. */
    SDDF_ERR_NO_BUF = -2,
    /* Pbuf successfully enqueued to be sent later. */
    SDDF_ERR_ENQUEUED    = -3,
    /* Could not resolve error. */
    SDDF_ERR_UNHANDLED    = -4
} net_sddf_err_t;

/**
 * Function type for output of sDDF LWIP errors.
 */
typedef int (*sddf_lwip_err_output_fn)(const char *format, ...);

/**
 * Function type for netif status callback. Invoked by LWIP upon
 * successfully obtaining an IP address for the network interface.
 */
typedef void (*sddf_lwip_netif_status_callback_fn)(char *ip_addr);

/**
 * Function type for handling function which is optionally invoked
 * when a pbuf is unable to be sent due to no available sDDF tx buffers.
 * Can be used to store pbuf until more buffers are available.
 */
typedef net_sddf_err_t (*sddf_lwip_handle_empty_tx_free_fn)(struct pbuf *p);

/** 
 * Checks LWIP system timeouts. Should be invoked after every LWIP tick.
 */
void sddf_lwip_process_timeout(void);

/**
 * Transmits the provided pbuf through the sddf network system.
 *
 * @param p pbuf to be transmitted.
 *
 * @return If the pbuf is sent successfully, SDDF_ERR_OK is returned and the
 * pbuf can safely be freed. If the pbuf is too large, SDDF_ERR_PBUF is
 * returned. If there are no free sDDF buffers available,
 * handle_empty_tx_free will be called with the pbuf, and the return value
 * will be returned.
 */
net_sddf_err_t sddf_lwip_transmit_pbuf(struct pbuf *p);

/** 
 * Handles the passing of incoming packets in sDDF buffers to LWIP. Must be
 * called to process the sDDF RX queue each time a notification is received
 * from the network virtualiser.
 */
void sddf_lwip_process_rx(void);

/**
 * Handles the sending of notifications to the network RX and TX virtualisers.
 * Must be invoked at the end of each event handling loop and initialisation
 * to ensure outgoing buffers are processed by the virtualisers.
 */
void sddf_lwip_maybe_notify(void);

/**
 * Initialisation function for the sDDF LWIP library. Must be called prior
 * to using any other library functions.
 *
 * @param rx_queue RX net queue handle data structure. Must be initialised
 * prior to being passed to this function.
 * @param tx_queue TX net queue handle data structure. Must be initialised
 * prior to being passed to this function.
 * @param rx_ch RX notification channel to the net RX virtualiser.
 * @param tx_ch TX notification channel to the net TX virtualiser.
 * @param rx_buffer_data_region virtual address of the start of the RX
 * buffer region.
 * @param tx_buffer_data_region virtual address of the start of the TX
 * buffer region.
 * @param timer_ch timer notification channel to the timer driver.
 * @param mac mac address of the client.
 * @param err_output function pointer to optional user provided error
 * output function. Provide NULL to use default sddf_printf_.
 * @param netif_callback function pointer to optional user provided netif
 * status callback function. Provide NULL to use err_output to print client
 * MAC address and obtained IP address.
 * @param handle_empty_tx_free function pointer to optional user provided
 * handling function for no available sDDF TX buffers during sending of LWIP
 * pbuf. Provide NULL to leave unhandled.
 */
void sddf_lwip_init(net_queue_handle_t rx_queue, net_queue_handle_t tx_queue,
                    microkit_channel rx_ch, microkit_channel tx_ch,
                    uintptr_t rx_buffer_data_region,
                    uintptr_t tx_buffer_data_region,
                    microkit_channel timer_ch,
                    uint64_t mac, sddf_lwip_err_output_fn err_output,
                    sddf_lwip_netif_status_callback_fn netif_callback,
                    sddf_lwip_handle_empty_tx_free_fn handle_empty_tx_free);