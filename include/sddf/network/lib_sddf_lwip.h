/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <sddf/resources/common.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/timer/config.h>
#include "lwip/pbuf.h"

/* Default ethernet MTU. */
#define SDDF_LWIP_ETHER_MTU 1500

/* Definitions for sDDF error constants. */
typedef enum {
    /* No error, everything OK. */
    SDDF_LWIP_ERR_OK = 0,
    /* Pbuf too large for sDDF buffer. */
    SDDF_LWIP_ERR_PBUF = -1,
    /* No buffers available. */
    SDDF_LWIP_ERR_NO_BUF = -2,
    /* Pbuf successfully enqueued to be sent later. */
    SDDF_LWIP_ERR_ENQUEUED = -3,
    /* Could not resolve error. */
    SDDF_LWIP_ERR_UNHANDLED = -4
} net_sddf_err_t;

#define SDDF_LIB_SDDF_LWIP_MAGIC_LEN 5

typedef struct lib_sddf_lwip_config {
    char magic[SDDF_LIB_SDDF_LWIP_MAGIC_LEN];
    region_resource_t pbuf_pool;
    uint64_t num_pbufs;
} lib_sddf_lwip_config_t;

/**
 * Function type for output of sDDF LWIP errors.
 */
typedef int (*sddf_lwip_err_output_fn)(const char *format, ...) __attribute__((format(__printf__, 1, 2)));

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
 * @return If the pbuf is sent successfully, SDDF_LWIP_ERR_OK is returned and the
 * pbuf can safely be freed. If the pbuf is too large, SDDF_LWIP_ERR_PBUF is
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
 * @param lib_sddf_lwip_config config structure for this library
 * @param net_config sDDF-Net config resource structure
 * @param timer_config sDDF-Timer config resource structure
 * @param rx_queue RX net queue handle data structure. Must be initialised
 * prior to being passed to this function.
 * @param tx_queue TX net queue handle data structure. Must be initialised
 * prior to being passed to this function.
 * @param err_output function pointer to optional user provided error
 * output function. Provide NULL to use default sddf_printf_.
 * @param netif_callback function pointer to optional user provided netif
 * status callback function. Provide NULL to use err_output to print client
 * MAC address and obtained IP address.
 * @param handle_empty_tx_free function pointer to optional user provided
 * handling function for no available sDDF TX buffers during sending of LWIP
 * pbuf. Provide NULL to leave unhandled.
 */
void sddf_lwip_init(lib_sddf_lwip_config_t *lib_sddf_lwip_config, net_client_config_t *net_config,
                    timer_client_config_t *timer_config, net_queue_handle_t rx_queue, net_queue_handle_t tx_queue,
                    sddf_lwip_err_output_fn err_output, sddf_lwip_netif_status_callback_fn netif_callback,
                    sddf_lwip_handle_empty_tx_free_fn handle_empty_tx_free);
