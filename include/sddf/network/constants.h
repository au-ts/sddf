/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <stdint.h>
#include <sddf/network/util.h>

#define ETH_TYPE_ARP 0x0806U
#define ETH_TYPE_IP 0x0800U
#define ETH_HWADDR_LEN 6
#define ETHARP_OPCODE_REQUEST 1
#define ETHARP_OPCODE_REPLY 2
#define IP_PROTOCOL_ICMP 0x01
#define IP_PROTOCOL_TCP 0x06
#define IP_PROTOCOL_UDP 0x11

#define NET_BUFFER_SIZE 2048

struct ethernet_address {
  uint8_t addr[6];
} __attribute__((packed));

struct ethernet_header {
  struct ethernet_address dest;
  struct ethernet_address src;
  uint16_t type;
} __attribute__((packed));

struct ipv4_header {
    uint8_t ihl : 4;
    uint8_t version : 4;
    uint8_t ecn : 2;
    uint8_t dscp : 6;
    uint16_t tot_len;
    uint16_t id;
    uint8_t frag_offset1 : 5;
    uint8_t more_frag : 1;
    uint8_t no_frag : 1;
    uint8_t reserved : 1;
    uint8_t frag_offset2;
    uint8_t ttl;
    uint8_t protocol;
    uint16_t check;
    uint32_t src_ip;
    uint32_t dst_ip;
} __attribute__((__packed__));

struct udp_header {
    uint16_t src_port;
    uint16_t dst_port;
    uint16_t len;
    uint16_t check;
} __attribute__((__packed__));

struct tcp_header {
    uint16_t src_port;
    uint16_t dst_port;
    uint32_t seq;
    uint32_t ack_seq;
    uint16_t reserved : 4;
    uint16_t doff : 4;
    uint16_t fin : 1;
    uint16_t syn : 1;
    uint16_t rst : 1;
    uint16_t psh : 1;
    uint16_t ack : 1;
    uint16_t urg : 1;
    uint16_t ece : 1;
    uint16_t cwr : 1;
    uint16_t window;
    uint16_t check;
    uint16_t urg_ptr;
} __attribute__((__packed__));

struct icmp_header {
    uint8_t type;
    uint8_t code;
    uint16_t check;
} __attribute__((__packed__));

/**
 * IPv4 header length in bytes.
 *
 * @param ip_hdr address of IPv4 header.
 *
 * @return IPv4 header length in bytes.
 */
static inline uint8_t ipv4_header_length(struct ipv4_header *ip_hdr)
{
    return 4 * ip_hdr->ihl;
}

/**
 * IPv4 payload length in bytes.
 *
 * @param ip_hdr address of IPv4 header.
 *
 * @return IPv4 payload length in bytes.
 */
static inline uint16_t ipv4_payload_length(struct ipv4_header *ip_hdr)
{
    return HTONS(ip_hdr->tot_len) - ipv4_header_length(ip_hdr);
}

/**
 * Extract start address of IPv4 payload.
 *
 * @param ip_hdr address of IPv4 packet.
 *
 * @return address of IPv4 payload.
 */
static inline void *ipv4_payload_start(struct ipv4_header *ip_hdr)
{
    return (uint8_t *)ip_hdr + ipv4_header_length(ip_hdr);
}

/*
 * By default we assume that the hardware we are dealing with
 * cannot generate checksums on transmit. We use this macro
 * to know whether to calculate it in the IP stack.
 */
#if defined(CONFIG_PLAT_IMX8MM_EVK) || defined(CONFIG_PLAT_MAAXBOARD) || defined(CONFIG_PLAT_IMX8MP_EVK)               \
    || defined(CONFIG_PLAT_ODROIDC4) || defined(CONFIG_PLAT_STAR64) || defined(CONFIG_PLAT_HIFIVE_P550)                \
    || defined(CONFIG_PLAT_ODROIDC2)
#define NETWORK_HW_HAS_CHECKSUM
#elif defined(CONFIG_PLAT_BCM2711)
#define NETWORK_HW_HAS_TRANSPORT_CHECKSUM
#endif

#if defined(CONFIG_PLAT_BCM2711)
#define PBUF_LINK_ENCAPSULATION_HLEN 64
#define NETWORK_HW_HAS_TRANSPORT_CHECKSUM
#else
#define PBUF_LINK_ENCAPSULATION_HLEN 0
#endif
