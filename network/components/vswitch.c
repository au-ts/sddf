/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "os/sddf.h"
#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/network/mac802.h>
#include <sddf/network/config.h>
#include <sddf/network/ip.h>
#include <sddf/network/icmp.h>
#include <sddf/network/tcp.h>
#include <sddf/network/udp.h>
#include <sddf/network/util.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#define VSWITCH_WRONG_PORT 0xFF

__attribute__((__section__(".net_vswitch_config"))) net_vswitch_config_t config;

typedef struct vswitch_state {
    /**
     * Rx and Tx queues are shared with both the virtualisers and vswitch
     * clients. The queue arrays are ordered as follows:
     *
     * rx_queues[0 : num_ports] - client Rx queues rx_queues[num_ports] - Tx
     * virtualiser connection tx_queues[0 : num_ports] - client Tx queues
     * tx_queues[num_ports] - Rx virtualiser connection
     *
     * The Rx queue is mapped to the Tx virtualiser and vice versa, as it allows
     * the vswitch to handle the virtualiser queues the same way as the client
     * queues. When a packet is received from the Rx virtualiser, this is
     * handled as if the Rx virtualiser is transmitting a packet to the other
     * network clients. Similarly when a client transmits a packet, this is
     * handled as if the Tx virtualiser is receiving a packet from the client.
     */
    net_queue_handle_t rx_queues[SDDF_NET_MAX_CLIENTS];
    net_queue_handle_t tx_queues[SDDF_NET_MAX_CLIENTS];
    /**
     * For each vswitch client c, allow_list[c] encodes which clients client c
     * can transmit to:
     *
     * allow_list[c] & BIT(i) == 1 - client c can transmit to client i
     *
     */
    uint64_t allow_list[SDDF_NET_MAX_CLIENTS];
    /**
     * The number of valid ports/queues of the vswitch. If the vswitch has a
     * connection to the virtualisers, the connection sits at index
     * config.num_ports, so the number of valid ports/queues is config.num_ports
     * + 1. Else, there are config.num_ports valid ports\queues.
     */
    uint8_t max_ports;
} vswitch_state_t;

static vswitch_state_t state;

bool need_rx_signal[SDDF_NET_MAX_CLIENTS];
bool need_tx_signal[SDDF_NET_MAX_CLIENTS];

/**
 * In order to handle broadcast packets which need to be transmitted to multiple
 * vswitch clients and the virtualisers, we keep a reference count for each
 * buffer in the count field. We only return the buffer to the sender once the
 * count returns to 0.
 *
 * Additionally, for systems connected to the network where the NIC is
 * configured to add checksums to packets, we only transmit the packet to the
 * virtualisers once it has been sent to and returned by all vswitch clients. In
 * this case we set the tx_to_virt bit to 1, and transmit the packet to the Tx
 * virtualiser once the count field has returned to 0.
 */
typedef struct buffer_ref {
    uint8_t count : 6; // only need 6 bits for a maximum of 63 MAX_ClIENTS
    uint8_t reserved : 1;
    uint8_t tx_to_virt : 1;
} buffer_ref_t;

buffer_ref_t *buffer_refs;
buffer_ref_t *buffer_refs_start[SDDF_NET_MAX_CLIENTS];

/**
 * In sDDF network systems not containing a vswitch, network queues are always
 * configured to have the capacity to hold all the available buffers. This means
 * that if buffers are (erroneously) added to the system, queues can never be
 * filled past capacity. Thus network components do not check if a queue is full
 * prior to enqueuing. The addition of a vswitch breaks this assumption, since
 * now buffers belonging to many different vswitch client's data region can now
 * be enqueued in the Rx active/free queues of each client's copy component.
 *
 * To avoid adding fullness checks to the copiers, or incurring accidental
 * buffer loss, the vswitch is carefull to only enqueue the capacity number of
 * buffers into each copier's queue. Thus we maintain a count of how many
 * buffers have been enqueued in each copier's queue.
 */
uint32_t num_forwarded_bufs[SDDF_NET_MAX_CLIENTS];

#ifdef NETWORK_HW_HAS_CHECKSUM
/**
 * Clear IPv4 header checksums and supported (UDP, TCP, ICMP) transport layer
 * checksums for an outgoing packet.
 *
 * @param eth_frame address of the ethernet header of the packet.
 */
static void clear_checksums(ether_hdr_t *eth_frame)
{
    if ((uint16_t)*eth_frame->etype != HTONS(ETH_TYPE_IP)) {
        return;
    }

    ipv4_hdr_t *ip_header = (ipv4_hdr_t *)((void *)eth_frame + sizeof(ether_hdr_t));
    ip_header->check = 0x0;
    switch (ip_header->protocol) {
    case IPV4_PROTO_UDP: {
        udp_hdr_t *udp_header = (udp_hdr_t *)((void *)ip_header + ipv4_header_length(ip_header));
        udp_header->check = 0x0;
        break;
    }
    case IPV4_PROTO_TCP: {
        tcp_hdr_t *tcp_header = (tcp_hdr_t *)((void *)ip_header + ipv4_header_length(ip_header));
        tcp_header->check = 0x0;
        break;
    }
    case IPV4_PROTO_ICMP: {
        icmp_hdr_t *icmp_header = (icmp_hdr_t *)((void *)ip_header + ipv4_header_length(ip_header));
        icmp_header->check = 0x0;
        break;
    }
    default: {
        sddf_dprintf("VSWITCH|ERR: Unsupported IP protocol %u received checksums may not be cleared!\n",
            ip_header->protocol);
        break;
    }
    }
}
#endif

static bool forward_frame(uint8_t src_id, uint8_t dst_id, net_buff_desc_t *src_buf)
{
    /* Don't forward more than the destination queue's capacity before some
    buffers are returned */
    if (num_forwarded_bufs[dst_id] >= config.ports[dst_id].rx.num_buffers) {
        return false;
    }

    net_buff_desc_t dest_buf;
    dest_buf.len = src_buf->len;
    dest_buf.io_or_offset = src_buf->io_or_offset;
    /* Tag the owner of the buffer so the destination copier knows which data
    region it belongs to. Also, upon return the tag tells the vswitch how to
    free the buffer. */
    dest_buf.oid = src_id;

#ifdef NETWORK_HW_HAS_CHECKSUM
    /* Clear ethernet checksum if the destination is the virtualiser and the NIC
    generates checksums */
    if (dst_id == config.num_ports) {
        clear_checksums((ether_hdr_t *)(config.ports[src_id].tx_data.region.vaddr + src_buf->io_or_offset));
    }
#endif

    net_enqueue_active(&state.rx_queues[dst_id], dest_buf);
    need_rx_signal[dst_id] = true;
    num_forwarded_bufs[dst_id]++;

    /* Mark that this buffer has been passed once */
    int ref_index = src_buf->io_or_offset / NET_BUFFER_SIZE;
    buffer_refs_start[src_id][ref_index].count++;

    return true;
}

static bool vswitch_can_send_to(uint8_t src_id, uint8_t dst_id)
{
    return state.allow_list[src_id] & ((uint64_t)1 << dst_id);
}

static uint8_t mac_addr_find(const mac_addr_t *dest_macaddr)
{
    mac_addr_t *mac;
    /* Try matching each vswitch client MAC */
    for (uint8_t i = 0; i < config.num_ports; i++) {
        mac = &config.ports[i].mac_addr;
        if (mac802_addr_eq(mac->addr, dest_macaddr->addr)) {
            return i;
        }
    }

    /* Drop if there is no virt connected and we did not match against any port
    */
    if (state.max_ports == config.num_ports) {
        return VSWITCH_WRONG_PORT;
    }

    /* I tried so hard and got so far, and in the end it doesn't even matter -
    default to forward to external port */
    return config.num_ports;
}

static bool try_broadcast(uint8_t src_id, net_buff_desc_t *buffer)
{
    bool success = false;
    /**
     * Forward the broadcast to all vswitch clients that the source is allowed
     * to transmit to, excluding the source itself. Then forward the broadcast
     * to the virtualisers if they are connected and the client has permission
     * to transmit to the network.
     */
    for (uint8_t i = 0; i < state.max_ports; i++) {
        if (i != src_id && vswitch_can_send_to(src_id, i)) {
#ifdef NETWORK_HW_HAS_CHECKSUM
            /* To ensure that vswitch clients transmit packets with the correct
            * checksums to their peers, we enforce that all vswitch clients must
            * generate their own checksums in software. However, our NICs are
            * generally configured to add checksums in hardware during
            * transmission. Thus when vswitch clients broadcast packets, we
            * first transmit the packet with checksums to the other vswitch
            * clients, then once all clients have freed the packet we zero out
            * the checksums before passing to the virtualiser. */
            if (success && i == config.num_ports) {
                int ref_index = buffer->io_or_offset / NET_BUFFER_SIZE;
                buffer_refs_start[src_id][ref_index].tx_to_virt = 1;
                continue;
            }
#endif
            success |= forward_frame(src_id, i, buffer);
        }
    }
    return success;
}

static bool try_send(uint8_t src_id, const mac_addr_t *dest_macaddr, net_buff_desc_t *buffer)
{
    bool success = false;
    uint8_t dst_id = mac_addr_find(dest_macaddr);

    if (dst_id != VSWITCH_WRONG_PORT && vswitch_can_send_to(src_id, dst_id)) {
        success = forward_frame(src_id, dst_id, buffer);
    }
    return success;
}

/* Dequeue free buffers from an Rx free queue and return to the sender's Tx free
queue if the refcount is 0. Notify the sender if buffers were returned, and
their flag is set */
static void rx_return(uint8_t port_id)
{
    net_queue_handle_t *src = &state.rx_queues[port_id];
    net_queue_handle_t *dst;
    uint8_t dst_id;

    bool reprocess = true;
    while (reprocess) {
        while (!net_queue_empty_free(src)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(src, &buffer);
            assert(!err);

            int ref_index = buffer.io_or_offset / NET_BUFFER_SIZE;
            assert(buffer_refs_start[buffer.oid][ref_index].count != 0);

            buffer_refs_start[buffer.oid][ref_index].count--;
            num_forwarded_bufs[port_id]--;

            if (buffer_refs_start[buffer.oid][ref_index].count != 0) {
                continue;
            }

#ifdef NETWORK_HW_HAS_CHECKSUM
            /* This was a broadcast packet, it can be forwarded to the
            virtualisers now */
            if (buffer_refs_start[buffer.oid][ref_index].tx_to_virt) {
                buffer_refs_start[buffer.oid][ref_index].tx_to_virt = 0;
                bool success = forward_frame(buffer.oid, config.num_ports, &buffer);
                assert(success);
                continue;
            }
#endif

            /* Return the buffer to its owner */
            dst_id = buffer.oid;
            dst = &state.tx_queues[dst_id];
            buffer.oid = 0;
            err = net_enqueue_free(dst, buffer);
            assert(!err);

            need_tx_signal[dst_id] = true;
        }

        net_request_signal_free(src);
        reprocess = false;

        if (!net_queue_empty_free(src)) {
            net_cancel_signal_free(src);
            reprocess = true;
        }
    }
}

static void forward_traffic_from(uint8_t port_id)
{
    /* Read from the Tx active queue and transmit to the Rx active queues of the
    vswitch clients and virtualisers */
    net_queue_handle_t *src = &state.tx_queues[port_id];

    bool reprocess = true;
    while (reprocess) {
        while (!net_queue_empty_active(src)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(src, &buffer);
            assert(!err);

            if (buffer.io_or_offset % NET_BUFFER_SIZE
                || buffer.io_or_offset >= NET_BUFFER_SIZE * config.ports[port_id].tx.num_buffers) {
                sddf_dprintf(
                    "VSWITCH|LOG: Port provided offset %lx which is not buffer aligned or outside of buffer region\n",
                    buffer.io_or_offset);
                err = net_enqueue_free(src, buffer);
                assert(!err);
                continue;
            }

            const char *frame_data = config.ports[port_id].tx_data.region.vaddr + buffer.io_or_offset;
            const ether_hdr_t *macaddr = (ether_hdr_t *)frame_data;
            bool transmitted = false;

            if (mac802_addr_is_bcast(macaddr->dest.addr)) {
                transmitted = try_broadcast(port_id, &buffer);
            } else {
                transmitted = try_send(port_id, &macaddr->dest, &buffer);
            }

            if (!transmitted) {
                net_enqueue_free(src, buffer);
                need_tx_signal[port_id] = true;
            }
        }

        net_request_signal_active(src);
        reprocess = false;

        if (!net_queue_empty_active(src)) {
            net_cancel_signal_active(src);
            reprocess = true;
        }
    }
}

void notified(sddf_channel ch)
{
    for (uint8_t i = 0; i < state.max_ports; i++) {
        if (ch == config.ports[i].tx.id) {
            forward_traffic_from(i);
            break;
        } else if (ch == config.ports[i].rx.id) {
            rx_return(i);
            break;
        }
    }

    for (uint8_t i = 0; i < state.max_ports; i++) {
        if (need_rx_signal[i] && net_require_signal_active(&state.rx_queues[i])) {
            net_cancel_signal_active(&state.rx_queues[i]);
            need_rx_signal[i] = false;
            sddf_notify(config.ports[i].rx.id);
        }
        if (need_tx_signal[i] && net_require_signal_free(&state.tx_queues[i])) {
            net_cancel_signal_free(&state.tx_queues[i]);
            need_tx_signal[i] = false;
            sddf_notify(config.ports[i].tx.id);
        }
    }
}

void init(void)
{
    assert(net_config_check_magic(&config));

    buffer_refs = (buffer_ref_t *)config.buffer_metadata.vaddr;
    buffer_refs_start[0] = buffer_refs;

    /* If no RX DMA buffers are present for the last port it means there is no
    virtualiser connected */
    state.max_ports = config.num_ports;
    if (config.ports[config.num_ports].tx.num_buffers) {
        state.max_ports++;
    }

    /* Set up queues and buffers references */
    for (uint8_t i = 0; i < state.max_ports; i++) {
        net_queue_init(&state.rx_queues[i], config.ports[i].rx.free_queue.vaddr, config.ports[i].rx.active_queue.vaddr,
                       config.ports[i].rx.num_buffers);
        net_queue_init(&state.tx_queues[i], config.ports[i].tx.free_queue.vaddr, config.ports[i].tx.active_queue.vaddr,
                       config.ports[i].tx.num_buffers);

        /* Set the allow_list based on predefined settings */
        state.allow_list[i] = config.ports[i].acl;

        /* Pre-calculate the start of the buffer reference count for each client
        for faster reference count calculations */
        if (i > 0) {
            buffer_refs_start[i] = buffer_refs_start[i - 1] + config.ports[i - 1].tx.num_buffers;
        }
    }
}
