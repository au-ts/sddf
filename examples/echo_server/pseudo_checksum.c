/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <sddf/util/util.h>
#include <sddf/network/constants.h>
#include <sddf/network/lib_sddf_lwip.h>
#include <sddf/network/util.h>
#include "pseudo_checksum.h"
#include "lwip/pbuf.h"

/* Shared ethernet.h definitions from GENET driver */

#define STATUS_TX_CSUM_PROTO_UDP    BIT(15)    /* Calculate UDP/TCP checksum */
#define STATUS_TX_CSUM_LV           BIT(31)    /* Enable transmit checksum offloading */

/* TSB structure for BCM GENET hardware checksum offload */
struct bcmgenet_tsb {
    uint32_t length_status;      /* length and peripheral status */
    uint32_t ext_status;         /* Extended status*/
    uint32_t rx_csum;            /* partial rx checksum */
    uint32_t unused1[9];         /* unused */
    /**
     * Tx checksum info.
     * Bits 14-0 contain the checksum destination offset.
     * Bit 15 calculate UDP/TCP checksum.
     * Bits 30-16 contain the offset of first byte to be checksummed.
     * Bit 31 enables checksum offloading.
     * Note the transport layer header must be initialised with pseudo header checksum.
     */
    uint32_t tx_csum_info;
    uint32_t unused2[3];         /* unused */
};

struct bcmgenet_tsb device_checksum;

/* Temporary pbuf used to pre-pend packets with TSB data. */
struct pbuf checksum_pbuf;

/* Pseudo-header used for UDP/TCP checksum calculation */
typedef struct pseudo_header {
    uint32_t src_ip;
    uint32_t dst_ip;
    /* Always set to 0 */
    uint8_t reserved;
    uint8_t protocol;
    /* Transport layer packet length */
    uint16_t len;
} pseudo_header_t;

/* Minimum ethernet frame size */
#define MIN_ETH_PKT_LEN 60

bool pbuf_needs_checksum(struct pbuf *p)
{
    if (p == &checksum_pbuf) {
        return false;
    }
    return true;
}

net_sddf_err_t add_checksum_and_transmit(struct pbuf *p)
{
    /* Construct pbuf to prepend to packet pbuf */
    checksum_pbuf.payload = &device_checksum;
    checksum_pbuf.len = sizeof(struct bcmgenet_tsb);
    checksum_pbuf.next = p;
    checksum_pbuf.tot_len = sizeof(struct bcmgenet_tsb) + p->tot_len;

    struct ethernet_header *eth_hdr = (struct ethernet_header *)p->payload;
    switch (eth_hdr->type) {
    case HTONS(ETH_TYPE_ARP): {
        /**
         * No checksum is needed for ARP packets, so we point the hardware to
         * the end of the packet to start calculation. If the packet is less
         * than the minimum 60-byte frame, we point to the minimum padded size.
         * */
        device_checksum.tx_csum_info = MAX(MIN_ETH_PKT_LEN, p->tot_len) << 16 | MAX(MIN_ETH_PKT_LEN, p->tot_len);
        break;
    }
    case HTONS(ETH_TYPE_IP): {
        struct ipv4_header *ip_hdr = (struct ipv4_header *)((void *)p->payload + sizeof(struct ethernet_header));

        bool supported = true;
        bool pseudo = true;
        uintptr_t checksum_addr = 0;
        switch (ip_hdr->protocol) {
        case IP_PROTOCOL_UDP: {
            struct udp_header *udp_hdr = (struct udp_header *)ipv4_payload_start(ip_hdr);
            /* UDP header checksum must lie within this pbuf's payload so pseudo header checksum can be written */
            assert(p->len >= sizeof(struct ethernet_header) + ipv4_header_length(ip_hdr) + sizeof(struct udp_header));
            checksum_addr = (uintptr_t)&udp_hdr->check;
            break;
        }
        case IP_PROTOCOL_TCP: {
            struct tcp_header *tcp_hdr = (struct tcp_header *)ipv4_payload_start(ip_hdr);
            /* TCP header checksum must lie within this pbuf's payload so pseudo header checksum can be written */
            assert(p->len >= sizeof(struct ethernet_header) + ipv4_header_length(ip_hdr) + sizeof(struct tcp_header));
            checksum_addr = (uintptr_t)&tcp_hdr->check;
            break;
        }
        case IP_PROTOCOL_ICMP: {
            struct icmp_header *icmp_hdr = (struct icmp_header *)ipv4_payload_start(ip_hdr);
            checksum_addr = (uintptr_t)&icmp_hdr->check;
            pseudo = false;
            break;
        }
        default:
            supported = false;
            break;
        }

        if (!supported) {
            device_checksum.tx_csum_info = MAX(MIN_ETH_PKT_LEN, p->tot_len) << 16 | MAX(MIN_ETH_PKT_LEN, p->tot_len);
            break;
        }

        if (pseudo) {
            /* Construct pseudo header */
            pseudo_header_t pseudo_data = { ip_hdr->src_ip, ip_hdr->dst_ip, 0, ip_hdr->protocol,
                                            HTONS(ipv4_payload_length(ip_hdr)) };

            /* Sum up the pseudo-header */
            uint32_t sum = 0;
            uint16_t *pseudo_data_ptr = (uint16_t *)&pseudo_data;
            for (uint8_t i = 0; i < sizeof(pseudo_header_t) / sizeof(uint16_t); i++) {
                sum += pseudo_data_ptr[i];
            }

            /* Fold 32-bit sum to 16 bits (one's complement sum) */
            while (sum >> 16) {
                sum = (sum & 0xFFFF) + (sum >> 16);
            }

            /* Set packet checksum to pseudo checksum */
            *(uint16_t *)checksum_addr = sum;
        }

        device_checksum.tx_csum_info = STATUS_TX_CSUM_LV | STATUS_TX_CSUM_PROTO_UDP
                                     | checksum_addr - (uintptr_t)p->payload // checksum destination offset
                                     | ((uintptr_t)ipv4_payload_start(ip_hdr) - (uintptr_t)p->payload)
                                           << 16; // start byte
        break;
    }
    default:
        device_checksum.tx_csum_info = MAX(MIN_ETH_PKT_LEN, p->tot_len) << 16 | MAX(MIN_ETH_PKT_LEN, p->tot_len);
        break;
    }

    return sddf_lwip_transmit_pbuf(&checksum_pbuf);
}
