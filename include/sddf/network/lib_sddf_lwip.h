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
    SDDF_LWIP_ERR_LARGE_PBUF = -1,
    /* Pbuf is NULL or from the wrong memory pool. */
    SDDF_LWIP_ERR_INVALID_PBUF = -2,
    /* No buffers available. */
    SDDF_LWIP_ERR_NO_BUF = -3,
    /* Unknown lwIP error. */
    SDDF_LWIP_ERR_UNHANDLED = -4
} net_sddf_err_t;

#define SDDF_LIB_SDDF_LWIP_MAGIC_LEN 5

typedef struct lib_sddf_lwip_config {
    char magic[SDDF_LIB_SDDF_LWIP_MAGIC_LEN];
    region_resource_t pbuf_pool;
    uint64_t num_pbufs;
} lib_sddf_lwip_config_t;

/* Wrapper over custom_pbuf structure to keep track of buffer's offset into data
region. */
typedef struct pbuf_custom_offset {
    struct pbuf_custom custom;
    uint64_t offset;
} pbuf_custom_offset_t;

/**
 * Function type for output of sDDF lwIP errors.
 */
typedef int (*sddf_lwip_err_output_fn)(const char *format, ...) __attribute__((format(__printf__, 1, 2)));

/**
 * Function type for netif status callback. Invoked by lwIP upon
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
 * Function type for checking whether the transmission of a pbuf should be
 * intercepted and handled by the provided TX handle intercept function.
 */
typedef bool (*sddf_lwip_tx_intercept_condition_fn)(struct pbuf *p);

/**
 * Function type for handling the transmission of pbufs which satisfy the
 * provided TX intercept condition function.
 */
typedef net_sddf_err_t (*sddf_lwip_tx_handle_intercept_fn)(struct pbuf *p);

/**
 * Check whether the pbuf pool is empty.
 *
 * @return true if pbuf pool is empty, false otherwise.
 */
bool pbuf_pool_empty(void);

/**
 * Allocate a pbuf from lib sDDF lwIP static pbuf pool.
 *
 * @return pointer to allocated pbuf or NULL if out of memory.
 */
pbuf_custom_offset_t *pbuf_pool_alloc(void);

/**
 * Free a pbuf allocated from lib sDDF lwIP static pbuf pool. WARNING: This
 * function only checks if p is a valid pbuf pointer from the memory pool, not
 * if it is currently allocated. Freeing a pbuf that is already free will cause
 * pbufs to be permanently lost.
 *
 * @param p pbuf to free.
 *
 * @return SDDF_LWIP_ERR_OK pbuf freed succesfully.
 * @return SDDF_LWIP_ERR_INVALID_PBUF pbuf is not part of lib sDDF lwIP static
 * pbuf pool.
 */
net_sddf_err_t pbuf_pool_free(pbuf_custom_offset_t *pbuf);

/**
 * Checks lwIP system timeouts. Should be invoked after every lwIP tick.
 */
void sddf_lwip_process_timeout(void);

/**
 * Transmits the provided pbuf through the sddf network system. If there are no
 * free sDDF buffers available, handle_empty_tx_free will be called with the
 * pbuf, and the return value will be returned.
 *
 * @param p pbuf to be transmitted.
 *
 * @return SDDF_LWIP_ERR_OK pbuf was sent successfully.
 * @return SDDF_LWIP_ERR_LARGE_PBUF pbuf is larger than sDDF net buffer.
 * @return SDDF_LWIP_ERR_NO_BUF no available sDDF buffers, or lib sDDF lwIP does
   not have Tx enabled.
 * @return SDDF_LWIP_ERR_UNHANDLED unhandled lwIP error occured.
 */
net_sddf_err_t sddf_lwip_transmit_pbuf(struct pbuf *p);

/**
 * Handles the passing of incoming packets in sDDF buffers to lwIP. Must be
 * called to process the sDDF RX queue each time a notification is received from
 * the network virtualiser. If client is TX only calling this function has no
 * effect.
 */
void sddf_lwip_process_rx(void);

/**
 * Input a user provided pbuf into lwIPs network stack. User is responsible for
 * freeing the pbuf in the case of failure.
 *
 * @param p initialised pbuf to input.
 *
 * @return SDDF_LWIP_ERR_OK pbuf was input successfully.
 * @return SDDF_LWIP_ERR_INVALID_PBUF invalid pbuf pointer.
 * @return SDDF_LWIP_ERR_UNHANDLED unhandled lwIP error occured.
 */
net_sddf_err_t sddf_lwip_input_pbuf(struct pbuf *p);

/**
 * Handles the sending of notifications to the network RX and TX virtualisers.
 * Must be invoked at the end of each event handling loop and initialisation
 * to ensure enqueued buffers are processed by the virtualisers.
 */
void sddf_lwip_maybe_notify(void);

/**
 * Initialisation function for the sDDF lwIP library. Must be called prior to
 * using any other sDDF lwIP library functions.
 *
 * @param lib_sddf_lwip_config config structure for this library
 * @param net_config sDDF-Net config resource structure
 * @param timer_config sDDF-Timer config resource structure
 * @param rx_queue RX net queue handle data structure. If client is TX only, set
 * capacity to 0.
 * @param tx_queue TX net queue handle data structure.  If client is RX only,
 * set capacity to 0.
 * @param ip_addr IP address of client as a string if IP is fixed. Set to NULL
 * if DHCP is required to obtain IP address. WARNING: If provided, ip_addr
 * string must be '\0' terminated.
 * @param err_output function pointer to optional user provided error output
 * function. Provide NULL to use default sddf_printf_.
 * @param netif_callback function pointer to optional user provided netif status
 * callback function. Provide NULL to use err_output to print client MAC address
 * and obtained IP address.
 * @param handle_empty_tx_free function pointer to optional user provided
 * handling function for no available sDDF TX buffers during sending of lwIP
 * pbuf. Provide NULL to leave unhandled.
 * @param tx_intercept_condition function pointer to optional user provided TX
 * interception check function. Allows users to intercept lwIP transmissions
 * before they are enqueued in sDDF net TX queue. Return true to invoke TX
 * intercept handling function.
 * @param tx_handle_intercept function pointer to optional user provided TX
 * intercept handling function. If TX intercept condition function returns true
 * for a pbuf, the TX intercept handle function will be invoked to handle the
 * transmission of the pbuf.
 */
void sddf_lwip_init(lib_sddf_lwip_config_t *lib_sddf_lwip_config, net_client_config_t *net_config,
                    timer_client_config_t *timer_config, net_queue_handle_t rx_queue, net_queue_handle_t tx_queue,
                    char *ip_addr, sddf_lwip_err_output_fn err_output,
                    sddf_lwip_netif_status_callback_fn netif_callback,
                    sddf_lwip_handle_empty_tx_free_fn handle_empty_tx_free,
                    sddf_lwip_tx_intercept_condition_fn tx_intercept_condition,
                    sddf_lwip_tx_handle_intercept_fn tx_handle_intercept);
