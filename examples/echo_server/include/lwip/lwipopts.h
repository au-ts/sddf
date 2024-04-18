/*
 * Copyright 2020, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#pragma once

#include <stdlib.h>
#include <stdbool.h>
#include <sddf/network/constants.h>

#define NO_SYS                          1
#define LWIP_TIMERS                     1
#define LWIP_NETCONN                    0
#define LWIP_SOCKET                     0
#define LWIP_ICMP                       1
#define LWIP_RAND                       rand
#define LWIP_DHCP                       1

#define MEM_ALIGNMENT                   4
#define MEM_SIZE                        0x30000

#define ETHARP_SUPPORT_STATIC_ENTRIES   1
#define SYS_LIGHTWEIGHT_PROT            0
#define LWIP_NETIF_STATUS_CALLBACK      1

/* Leave the checksum checking on RX to hardware */
#define CHECKSUM_CHECK_IP               0
#define CHECKSUM_CHECK_UDP              0
#define CHECKSUM_CHECK_TCP              0
#define CHECKSUM_CHECK_ICMP             0
#define CHECKSUM_CHECK_ICMP6            0

#ifdef NETWORK_HW_HAS_CHECKSUM

/* Leave the checksum checking on tx to hw */
#define CHECKSUM_GEN_IP                 0
#define CHECKSUM_GEN_UDP                0
#define CHECKSUM_GEN_TCP                0
#define CHECKSUM_GEN_ICMP               0
#define CHECKSUM_GEN_ICMP6              0

#else

#define CHECKSUM_GEN_IP                 1
#define CHECKSUM_GEN_UDP                1
#define CHECKSUM_GEN_TCP                1
#define CHECKSUM_GEN_ICMP               1
#define CHECKSUM_GEN_ICMP6              1

#endif

#define TCP_MSS 2000 // maximum segment size, max size of a single packet
#define TCP_WND 2000000 // tcp window, max data we can receive at once
#define TCP_SND_BUF TCP_WND // send buffer space
#define TCP_SNDLOWAT TCP_MSS

#define TCP_QUEUE_OOSEQ 1 // hold out-of-sequence packets instead of immediately dropping them
#define LWIP_TCP_SACK_OUT 1 // support sending selective acknowledgements

#define LWIP_WND_SCALE 1 // support window sizes > 65536
#define TCP_RCV_SCALE 12

#define LWIP_TCP_TIMESTAMPS 1 // support tcp timestamp option

#define PBUF_POOL_SIZE 1000
#define MEMP_NUM_PBUF TCP_SND_QUEUELEN
#define MEMP_NUM_TCP_SEG TCP_SND_QUEUELEN
#define MEMP_NUM_SYS_TIMEOUT 512

/* Set this to 0 for performance */
#define LWIP_STATS 0

/* So we can mark a pbuf as in use or not if we need to enqueue for later */
#define LWIP_PBUF_CUSTOM_DATA \
    bool in_use; \
    struct pbuf *next_chain;

#define LWIP_PBUF_INIT_CUSTOM_DATA(p) \
    (p)->in_use = false; \
    (p)->next_chain = NULL;

/* Debugging options */
#define LWIP_DEBUG // we always want this on
#define LWIP_DBG_MIN_LEVEL LWIP_DBG_LEVEL_WARNING // set this to 0 to see debug warnings

#define MEMP_DEBUG LWIP_DBG_ON
#define IP_DEBUG LWIP_DBG_ON
#define TCP_OUTPUT_DEBUG LWIP_DBG_ON
#define TCP_INPUT_DEBUG LWIP_DBG_ON