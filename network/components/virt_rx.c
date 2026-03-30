/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/network/config.h>
#include <sddf/network/constants.h>
#include <sddf/network/mac802.h>
#include <sddf/network/queue.h>
#include <sddf/network/util.h>
#include <sddf/util/cache.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>


typedef struct __attribute__((__packed__)) eth_hdr {
    /* destination MAC address */
    uint8_t ethdst_addr[ETH_HWADDR_LEN];
    /* source MAC address */
    uint8_t ethsrc_addr[ETH_HWADDR_LEN];
    /* if ethtype <= 1500 it holds the length of the frame. Otherwise, it holds
    the protocol of payload encapsulated in the frame */
    uint16_t ethtype;
} eth_hdr_t;

/* Length of ethernet header */
#define ETH_HDR_LEN sizeof(eth_hdr_t)

/* Ethernet type values */
#define ETH_TYPE_IP 0x0800U /* IPV4 packet */
#define ETH_TYPE_ARP 0x0806U /* ARP packet */

typedef struct __attribute__((__packed__)) ipv4_hdr {
    /* internet header length in 32-bit words, variable due to optional fields */
    uint8_t ihl:4;
    /* IP version, always 4 for IPv4 */
    uint8_t version:4;
    /* explicit congestion notification, optional */
    uint8_t ecn:2;
    /* differentiated services code point */
    uint8_t dscp:6;
    /* total packet length in bytes, including header and data */
    uint16_t tot_len;
    /* identifier of packet, used in packet fragmentation */
    uint16_t id;
    /* offset in 8 bytes of fragment relative to the beginning of the original
    unfragmented IP datagram. Fragment offset is a 13 byte value split accross
    frag_offset1 and frag_offset2 */
    uint8_t frag_offset1:5;
    /* if packet belongs to fragmented group, 1 indicates this is not the last
    fragment */
    uint8_t more_frag:1;
    /* specifies whether datagram can be fragmented or not */
    uint8_t no_frag:1;
    /* reserved, set to 0 */
    uint8_t reserved:1;
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

/* Offset of the start of the IPV4 header */
#define IPV4_HDR_OFFSET ETH_HDR_LEN

/* Length of IPv4 header with no optional fields */
#define IPV4_HDR_LEN_MIN sizeof(ipv4_hdr_t)

/* IPv4 differentiated services code point values */
#define IPV4_DSCP_NET_CTRL 48 /* Network control */

/* IPv4 transport layer protocols */
#define IPV4_PROTO_ICMP 0x01
#define IPV4_PROTO_TCP 0x06
#define IPV4_PROTO_UDP 0x11

#define IPV4_ADDR_BUFLEN 16

static char ip_addr_buf0[IPV4_ADDR_BUFLEN];
static char ip_addr_buf1[IPV4_ADDR_BUFLEN];

/**
 * Convert a big-endian ip address integer to a string.
 *
 * @param ip big-endian ip address.
 * @param buf buffer used to output ip address as a string.
 *
 * @return buffer or NULL upon failure.
 */
static inline char *ipaddr_to_string(uint32_t ip, char *buf)
{
    char inv[3], *rp;
    uint8_t *ap, rem, n, i;
    int len = 0;

    rp = buf;
    ap = (uint8_t *)&ip;
    for (n = 0; n < 4; n++) {
        i = 0;
        do {
            rem = *ap % (uint8_t)10;
            *ap /= (uint8_t)10;
            inv[i++] = (char)('0' + rem);
        } while (*ap);
        while (i--) {
            if (len++ >= IPV4_ADDR_BUFLEN) {
                return NULL;
            }
            *rp++ = inv[i];
        }
        if (len++ >= IPV4_ADDR_BUFLEN) {
            return NULL;
        }
        *rp++ = '.';
        ap++;
    }
    *--rp = 0;
    return buf;
}

/* Used to signify that a packet has come in for the broadcast address and does not match with
 * any particular client. */
#define BROADCAST_ID (-2)

__attribute__((__section__(".net_virt_rx_config"))) net_virt_rx_config_t config;

/* In order to handle broadcast packets where the same buffer is given to multiple clients
  * we keep track of a reference count of each buffer and only hand it back to the driver once
  * all clients have returned the buffer. */
uint32_t *buffer_refs;

typedef struct state {
    net_queue_handle_t rx_queue_drv;
    net_queue_handle_t rx_queue_clients[SDDF_NET_MAX_CLIENTS];
} state_t;

state_t state;

/* Boolean to indicate whether a packet has been enqueued into the driver's free queue during notification handling */
static bool notify_drv;

/* Return the client ID if the Mac address is a match to a client, return the broadcast ID if MAC address
  is a broadcast address, return -1 if we have not found the match. */
int get_mac_addr_match(struct ethernet_header *buffer)
{
    for (int client = 0; client < config.num_clients; client++) {
        for (int i = 0; i < config.clients[client].num_macs; i++) {
            ////sddf_printf_("VIRT RX MATCHING MAC from client: %d\n", client);
            ////sddf_printf_("SRC "PR_MAC802_ADDR"\n", PR_MAC802_SRC_ADDR_ARGS((struct ether_addr *)buffer));
            ////sddf_printf_("DST "PR_MAC802_ADDR"\n", PR_MAC802_DEST_ADDR_ARGS((struct ether_addr *)buffer));
            if (mac802_addr_eq(buffer->dest.addr, config.clients[client].mac_addrs[i].addr)) {
                return client;
            }
        }
    }

    if (mac802_addr_is_bcast(buffer->dest.addr)) {
        return BROADCAST_ID;
    }

    return -1;
}

void rx_return(void)
{
    bool reprocess = true;
    bool notify_clients[SDDF_NET_MAX_CLIENTS] = { false };
    while (reprocess) {
        while (!net_queue_empty_active(&state.rx_queue_drv)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&state.rx_queue_drv, &buffer);
            assert(!err);

            buffer.io_or_offset = buffer.io_or_offset - config.data.io_addr;
            uintptr_t buffer_vaddr = buffer.io_or_offset + (uintptr_t)config.data.region.vaddr;

            // Tag this as coming from the external network
            buffer.oid = SDDF_NET_MAX_CLIENTS - 1;

            // Cache invalidate after DMA write, so we don't read stale data.
            // This must be performed after the DMA write to avoid reading
            // data that was speculatively fetched before the DMA write.
            //
            // We would invalidate if it worked in usermode. Alas, it
            // does not -- see [1]. The fastest operation that works is a
            // usermode CleanInvalidate (faster than a Invalidate via syscall).
            //
            // [1]: https://developer.arm.com/documentation/ddi0595/2021-06/AArch64-Instructions/DC-IVAC--Data-or-unified-Cache-line-Invalidate-by-VA-to-PoC
            cache_clean_and_invalidate(buffer_vaddr, buffer_vaddr + buffer.len);
            int client = get_mac_addr_match((struct ethernet_header *) buffer_vaddr);

            struct eth_hdr * hdr = (struct eth_hdr *)buffer_vaddr;
            if (hdr->ethtype == HTONS(ETH_TYPE_IP)) {
                struct ipv4_hdr * ip = (struct ipv4_hdr *)(buffer_vaddr + sizeof(eth_hdr_t));
                if (ip->protocol == IPV4_PROTO_UDP) {
                    sddf_printf_("VIRT RX got SRC IP: %s DST IP: %s client: %d\n", ipaddr_to_string(ip->src_ip, ip_addr_buf0), ipaddr_to_string(ip->dst_ip, ip_addr_buf1), client);
                }
            }
            //sddf_printf_("VIRT RX active from client: %d\n", client);
            if (client == BROADCAST_ID) {
                int ref_index = buffer.io_or_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] == 0);
                // For broadcast packets, set the refcount to number of clients
                // in the system. Only enqueue buffer back to driver if
                // all clients have consumed the buffer.
                buffer_refs[ref_index] = config.num_clients;

                for (int i = 0; i < config.num_clients; i++) {
                    err = net_enqueue_active(&state.rx_queue_clients[i], buffer);
                    assert(!err);
                    notify_clients[i] = true;
                }
                continue;
            } else if (client >= 0) {
                int ref_index = buffer.io_or_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] == 0);
                buffer_refs[ref_index] = 1;

                err = net_enqueue_active(&state.rx_queue_clients[client], buffer);
                assert(!err);
                notify_clients[client] = true;
            } else {
                buffer.io_or_offset = buffer.io_or_offset + config.data.io_addr;
                err = net_enqueue_free(&state.rx_queue_drv, buffer);
                assert(!err);
                notify_drv = true;
            }
        }
        net_request_signal_active(&state.rx_queue_drv);
        reprocess = false;

        if (!net_queue_empty_active(&state.rx_queue_drv)) {
            net_cancel_signal_active(&state.rx_queue_drv);
            reprocess = true;
        }
    }

    for (int client = 0; client < config.num_clients; client++) {
        if (notify_clients[client] && net_require_signal_active(&state.rx_queue_clients[client])) {
            sddf_printf_("VIRT RX notifying client signal active: %d\n", client);
            net_cancel_signal_active(&state.rx_queue_clients[client]);
            sddf_notify(config.clients[client].conn.id);
        }
    }
}

void rx_provide(void)
{
    for (int client = 0; client < config.num_clients; client++) {
        bool reprocess = true;
        while (reprocess) {
            while (!net_queue_empty_free(&state.rx_queue_clients[client])) {
                net_buff_desc_t buffer;
                int err = net_dequeue_free(&state.rx_queue_clients[client], &buffer);
                assert(!err);
                assert(!(buffer.io_or_offset % NET_BUFFER_SIZE)
                       && (buffer.io_or_offset < NET_BUFFER_SIZE * state.rx_queue_drv.capacity));

                int ref_index = buffer.io_or_offset / NET_BUFFER_SIZE;
                //sddf_printf_("VIRT RX free ref_index: %d, buffer_refs: %d\n",ref_index, buffer_refs[ref_index]);
                assert(buffer_refs[ref_index] != 0);

                buffer_refs[ref_index]--;

                if (buffer_refs[ref_index] != 0) {
                    continue;
                }

                // To avoid having to perform a cache clean here we ensure that
                // the DMA region is only mapped in read only. This avoids the
                // case where pending writes are only written to the buffer
                // memory after DMA has occured.
                buffer.io_or_offset = buffer.io_or_offset + config.data.io_addr;
                err = net_enqueue_free(&state.rx_queue_drv, buffer);
                assert(!err);
                notify_drv = true;
            }

            net_request_signal_free(&state.rx_queue_clients[client]);
            reprocess = false;

            if (!net_queue_empty_free(&state.rx_queue_clients[client])) {
                net_cancel_signal_free(&state.rx_queue_clients[client]);
                reprocess = true;
            }
        }
    }

    if (notify_drv && net_require_signal_free(&state.rx_queue_drv)) {
        net_cancel_signal_free(&state.rx_queue_drv);
        sddf_deferred_notify(config.driver.id);
        notify_drv = false;
    }
}

void notified(sddf_channel ch)
{
    rx_return();
    rx_provide();
}

void init(void)
{
    assert(net_config_check_magic(&config));

    buffer_refs = config.buffer_metadata.vaddr;

    /* Set up client queues */
    for (int i = 0; i < config.num_clients; i++) {
        net_queue_init(&state.rx_queue_clients[i], config.clients[i].conn.free_queue.vaddr,
                       config.clients[i].conn.active_queue.vaddr, config.clients[i].conn.num_buffers);
    }

    /* Set up driver queues */
    net_queue_init(&state.rx_queue_drv, config.driver.free_queue.vaddr, config.driver.active_queue.vaddr,
                   config.driver.num_buffers);
    net_buffers_init(&state.rx_queue_drv, config.data.io_addr);

    if (net_require_signal_free(&state.rx_queue_drv)) {
        net_cancel_signal_free(&state.rx_queue_drv);
        sddf_deferred_notify(config.driver.id);
    }
}
