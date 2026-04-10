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

typedef struct client_info {
    uint32_t ip_addr;
    uint32_t id;
} client_info_t;

typedef struct clients {
    client_info_t info[SDDF_NET_MAX_CLIENTS - 1];
    uint32_t num;
} clients_t;

typedef struct vswitch_state {
    /* Queues ranging from 0 to num_ports - 1 belong to vswitch clients,
     * where client n's Rx and Tx queues are given by rx_queues[n] and tx_queues[n] respectively.
     * The queues at index num_ports are the queues the vswitch shares with the virtualiser.
     * Note that rx_queues[num_ports] is the Tx virtualiser queue, and tx_queues[num_ports] is the Rx virtualiser queue
     * - this allows the vswitch to handle virtualiser communication similarly to client communication.
     * When a packet is received from the Rx virtualiser, this is handled as if the Rx virtualiser
     * is transmitting a packet to the other network clients. Similarly when a client transmits a packet,
     * this is handled as if the Tx virtualiser is receiving a packet from the client. */
    net_queue_handle_t rx_queues[SDDF_NET_MAX_CLIENTS];
    net_queue_handle_t tx_queues[SDDF_NET_MAX_CLIENTS];
    uint64_t allow_list[SDDF_NET_MAX_CLIENTS];
    bool virt_connected;
    clients_t clients;
} vswitch_state_t;

static vswitch_state_t state;

bool need_rx_signal[SDDF_NET_MAX_CLIENTS];
bool need_tx_signal[SDDF_NET_MAX_CLIENTS];

typedef struct buffer_ref {
    uint8_t count : 6; // need just 6 bits for 63 MAX_ClIENTS
    uint8_t reserved : 1;
    uint8_t tx_to_virt : 1; // whether this buffer ultimately needs to be sent to virt
} buffer_ref_t;

buffer_ref_t *buffer_refs;
buffer_ref_t *buffer_refs_start[SDDF_NET_MAX_CLIENTS];
uint32_t num_forwarded_bufs[SDDF_NET_MAX_CLIENTS];

#ifdef NETWORK_HW_HAS_CHECKSUM
static void clear_checksums(ether_hdr_t *eth_frame)
{
    if ((uint16_t)*eth_frame->etype != HTONS(ETH_TYPE_IP)) {
        return;
    }

    ipv4_hdr_t *ip_header = (ipv4_hdr_t *)((void *)eth_frame + sizeof(ether_hdr_t));
    if (ip_header->protocol == IPV4_PROTO_UDP) {
        switch (ip_header->protocol) {
        case IPV4_PROTO_UDP: {
            udp_hdr_t *udp_header = (udp_hdr_t *)((void *)eth_frame + sizeof(ether_hdr_t) + sizeof(ipv4_hdr_t));
            udp_header->check = 0x0;
            break;
        }
        case IPV4_PROTO_TCP: {
            tcp_hdr_t *tcp_header = (tcp_hdr_t *)((void *)eth_frame + sizeof(ether_hdr_t) + sizeof(ipv4_hdr_t));
            tcp_header->check = 0x0;
            break;
        }
        case IPV4_PROTO_ICMP: {
            icmp_hdr_t *icmp_header = (icmp_hdr_t *)((void *)eth_frame + sizeof(ether_hdr_t) + sizeof(ipv4_hdr_t));
            icmp_header->check = 0x0;
            break;
        }
        default: {
            sddf_dprintf("VSWITCH|ERR: Wrong ip protocol received\n");
            break;
        }
        }
    }
}
#endif

static bool forward_frame(uint8_t src_id, uint8_t dst_id, net_buff_desc_t *src_buf)
{
    net_buff_desc_t d_buffer;

    d_buffer.len = src_buf->len;
    d_buffer.io_or_offset = src_buf->io_or_offset;
    /* Add a tag for the owner of this buffer so vswitch knows which reference slot to increment
     * Also, the copier will use this tag to know which buffer to address */
    d_buffer.oid = src_id;

    /* Don't forward more than the queue's capacity before some packets are returned */
    if (num_forwarded_bufs[dst_id] >= config.ports[dst_id].rx.num_buffers) {
        return false;
    }

#ifdef NETWORK_HW_HAS_CHECKSUM
    /* Clear ethernet checksum if the dest is a virtualiser, we already know other clients handled it */
    if (dst_id == config.num_ports) {
        clear_checksums((ether_hdr_t *)(config.ports[src_id].tx_data.region.vaddr + src_buf->io_or_offset));
    }
#endif

    net_enqueue_active(&state.rx_queues[dst_id], d_buffer);
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

uint8_t mac_addr_find(const mac_addr_t *dest_macaddr)
{
    mac_addr_t *mac;
    /* Try matching each MAC in the list (skip the virt port, config.num_ports) */
    for (uint8_t i = 0; i < config.num_ports; i++) {
        mac = &config.ports[i].mac_addr;
        if (mac802_addr_eq(mac->addr, dest_macaddr->addr)) {
            return i;
        }
    }

    /* Drop if no virt connected and did not match against any port */
    if (!state.virt_connected) {
        return VSWITCH_WRONG_PORT;
    }

    /* I tried so hard and got so far, and in the end it doesn't even matter - default to forward to external port */
    return config.num_ports;
}

static bool try_broadcast(uint8_t src_id, net_buff_desc_t *buffer)
{
    bool success = false;
    /* Only broadcast to allowed, exclude the source */
    for (uint8_t i = 0; i <= config.num_ports; i++) {
        if (i != src_id && vswitch_can_send_to(src_id, i)) {
#ifdef NETWORK_HW_HAS_CHECKSUM
            /* To ensure that vswitch clients transmit packets with the correct checksums to their peers,
             * we enforce that all vswitch clients must generate their own checksums in software.
             * However, our NICs are generally configured to add checksums in hardware during transmission.
             * Thus when vswitch clients broadcast packets, we first transmit the packet with checksums to the other vswitch clients,
             * then once all clients have freed the packet we zero out the checksums before passing to the virtualiser.
             * There is a corner case where a client can only transmit to the virtualiser yet still broadcasts.
             * In this case the packet will need to be forwarded immediately. */
            if (success && i == config.num_ports) {
                int ref_index = buffer->io_or_offset / NET_BUFFER_SIZE;
                buffer_refs_start[src_id][ref_index].tx_to_virt = 1;
                success = true;
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

/* Read free buffers from RX, see if the refcount is 0, and then return them to TX and notify the TX clients */
static void rx_return(uint8_t port_id)
{
    net_queue_handle_t *src = &state.rx_queues[port_id];
    net_queue_handle_t *dst;

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
            if (buffer_refs_start[buffer.oid][ref_index].tx_to_virt) {
                buffer_refs_start[buffer.oid][ref_index].tx_to_virt = 0;
                forward_frame(buffer.oid, config.num_ports, &buffer);
                continue;
            }
#endif

            /* Return the buffer to its owner */
            dst = &state.tx_queues[buffer.oid];
            err = net_enqueue_free(dst, buffer);
            assert(!err);

            need_tx_signal[buffer.oid] = true;
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
    /* Read from TX and fill in the corresponding RX (switched for virtualizer but we handle that in SDF) */
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
    for (uint8_t i = 0; i <= config.num_ports; i++) {
        if (ch == config.ports[i].tx.id) {
            forward_traffic_from(i);
            break;
        } else if (ch == config.ports[i].rx.id) {
            rx_return(i);
            break;
        }
    }

    for (uint8_t i = 0; i <= config.num_ports; i++) {
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

    /* If no RX DMA buffers are present for the last port it means there is no virtualiser connected */
    state.virt_connected = config.ports[config.num_ports].tx.num_buffers != 0;

    /* Set up client queues and buffers for copying? */
    for (uint8_t i = 0; i <= config.num_ports; i++) {
        net_queue_init(&state.rx_queues[i], config.ports[i].rx.free_queue.vaddr, config.ports[i].rx.active_queue.vaddr,
                       config.ports[i].rx.num_buffers);
        net_queue_init(&state.tx_queues[i], config.ports[i].tx.free_queue.vaddr, config.ports[i].tx.active_queue.vaddr,
                       config.ports[i].tx.num_buffers);

        /* Seed the allow_list based on predefined settings */
        state.allow_list[i] = config.ports[i].acl;

        /* Pre-calculate the buffer start indexing for faster reference */
        if (i > 0) {
            buffer_refs_start[i] = buffer_refs_start[i - 1] + config.ports[i - 1].tx.num_buffers;
        }
    }
}

seL4_MessageInfo_t protected(sddf_channel ch, seL4_MessageInfo_t msginfo)
{
    size_t label = microkit_msginfo_get_label(msginfo);
    switch (label) {
    case VSWITCH_REPORT_IP_ADDR: {
        uint32_t ip_addr = microkit_mr_get(0);
        uint32_t client_id = microkit_mr_get(1);
        state.clients.info[state.clients.num].ip_addr = ip_addr;
        state.clients.info[state.clients.num].id = client_id;
        state.clients.num += 1;
        sddf_dprintf("VSWITCH: PPC received REPORT PPC with label: %zu from ch: %u client_id: %d ip_addr: %d num_clients: %d\n", label, ch, client_id, ip_addr, state.clients.num);
        break;
    }
    case VSWITCH_QUERY_IP_ADDR: {
        sddf_dprintf("VSWITCH: PPC received QUERY PPC with label: %zu from ch: %u num_clients: %d\n", label, ch, state.clients.num);
        sddf_set_mr(0, state.clients.num);
        sddf_dprintf("VSWITCH: PPC reg: 0 val: %d\n", state.clients.num * 2 + 1);
        for (int i = 0; i < state.clients.num; i++) {
            sddf_set_mr(i * 2 + 1, state.clients.info[i].id);
            sddf_set_mr(i * 2 + 2, state.clients.info[i].ip_addr);
            sddf_dprintf("VSWITCH: PPC reg: %d val: %d\n", i * 2 + 1, state.clients.info[i].id);
            sddf_dprintf("VSWITCH: PPC reg: %d val: %d\n", i * 2 + 2, state.clients.info[i].ip_addr);
        }
        return seL4_MessageInfo_new(0, 0, 0, state.clients.num * 2 + 1);
    }
    default: {
        sddf_printf_("VSWITCH: PPC - Wrong label passed\n");
        break;
    }
    }
    return seL4_MessageInfo_new(0, 0, 0, 0);
}
