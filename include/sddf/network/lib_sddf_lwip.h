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
bool sddf_lwip_pbuf_pool_empty(void);

/**
 * Allocate a pbuf from lib sDDF lwIP static pbuf pool.
 *
 * @return pointer to allocated pbuf or NULL if out of memory.
 */
pbuf_custom_offset_t *sddf_lwip_pbuf_pool_alloc(void);

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
net_sddf_err_t sddf_lwip_pbuf_pool_free(pbuf_custom_offset_t *pbuf);

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

/**
 * Protocol headers for hanlding special cases of transmission packets.
 * Borrowed from the Lionsos/Firewall project.
 */
typedef struct __attribute__((__packed__)) sddf_eth_hdr {
    /* destination MAC address */
    uint8_t ethdst_addr[ETH_HWADDR_LEN];
    /* source MAC address */
    uint8_t ethsrc_addr[ETH_HWADDR_LEN];
    /* if ethtype <= 1500 it holds the length of the frame. Otherwise, it holds
    the protocol of payload encapsulated in the frame */
    uint16_t ethtype;
} eth_hdr_t;

typedef struct __attribute__((__packed__)) sddf_ipv4_hdr {
    /* internet header length in 32-bit words, variable due to optional fields */
    uint8_t ihl : 4;
    /* IP version, always 4 for IPv4 */
    uint8_t version : 4;
    /* explicit congestion notification, optional */
    uint8_t ecn : 2;
    /* differentiated services code point */
    uint8_t dscp : 6;
    /* total packet length in bytes, including header and data */
    uint16_t tot_len;
    /* identifier of packet, used in packet fragmentation */
    uint16_t id;
    /* offset in 8 bytes of fragment relative to the beginning of the original
    unfragmented IP datagram. Fragment offset is a 13 byte value split accross
    frag_offset1 and frag_offset2 */
    uint8_t frag_offset1 : 5;
    /* if packet belongs to fragmented group, 1 indicates this is not the last
    fragment */
    uint8_t more_frag : 1;
    /* specifies whether datagram can be fragmented or not */
    uint8_t no_frag : 1;
    /* reserved, set to 0 */
    uint8_t reserved : 1;
    /* offset in 8 bytes of fragment relative to the beginning of the original
    unfragmented IP datagram. Fragment offset is a 13 byte value split accross
    frag_offset1 and frag_offset2 */
    uint8_t frag_offset2;
    /* time to live, in seconds but in practice router hops */
    uint8_t ttl;
    /* transport layer protocol of encapsulated packet */
    uint8_t protocol;
    /* internet checksum of IPv4 header */
    uint16_t check;
    /* source IP address */
    uint32_t src_ip;
    /* destination IP address */
    uint32_t dst_ip;
    /* optional fields excluded */
} ipv4_hdr_t;

typedef struct __attribute__((__packed__)) sddf_udp_hdr {
    /* source port */
    uint16_t src_port;
    /* destination port */
    uint16_t dst_port;
    /* length in bytes of the UDP datagram including header */
    uint16_t len;
    /* checksum over the UDP datagram and psuedo-header, optional for IPv4 */
    uint16_t check;
} udp_hdr_t;

typedef struct __attribute__((__packed__)) tcp_hdr {
    /* source port */
    uint16_t src_port;
    /* destination port */
    uint16_t dst_port;
    /* sequence number */
    uint32_t seq;
    /* acknowledgement number */
    uint32_t ack_seq;
    /* reserved, set to 0 */
    uint16_t reserved : 4;
    /* size of the TCP header in 32 bit words */
    uint16_t doff : 4;
    /* fin */
    uint16_t fin : 1;
    /* syn */
    uint16_t syn : 1;
    /* reset */
    uint16_t rst : 1;
    /* push */
    uint16_t psh : 1;
    /* ack */
    uint16_t ack : 1;
    /* urgent pointer is valid */
    uint16_t urg : 1;
    /* ECN-Echo*/
    uint16_t ece : 1;
    /* congestion window reduced */
    uint16_t cwr : 1;
    /* size of the receive window*/
    uint16_t window;
    /* checksum over the TCP packet and psuedo-header */
    uint16_t check;
    /* urgent pointer */
    uint16_t urg_ptr;
    /* optional fields excluded */
} tcp_hdr_t;

#define ETH_HDR_LEN sizeof(eth_hdr_t)
#define IPV4_HDR_OFFSET ETH_HDR_LEN
#define IPV4_HDR_LEN_MIN sizeof(ipv4_hdr_t)

/* TSB structure for BCM GENET hardware chcksum offload */
struct bcmgenet_tsb {
    uint32_t length_status;      /* length and peripheral status */
    uint32_t ext_status;         /* Extended status*/
    uint32_t rx_csum;            /* partial rx checksum */
    uint32_t unused1[9];         /* unused */
    uint32_t tx_csum_info;       /* Tx checksum info. */
    uint32_t unused2[3];         /* unused */
};

#define SDDF_PROTO_IP       0x800
#define SDDF_PROTO_ARP      0x806
#define SDDF_PROTO_TCP      6
#define SDDF_PROTO_UDP      17
