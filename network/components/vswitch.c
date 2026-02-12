/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "sddf/network/config.h"
#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/vswitch.h>
#include <sddf/network/queue.h>
#include <sddf/network/mac802.h>
#include <sddf/network/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#define UNKNOWN_PORT -1

__attribute__((__section__(".net_vswitch_config"))) net_vswitch_config_t config;

/* These ports are analogous to ports on a physical switch.
* They represent a medium you can send to and receive from. */
/* For clients, incoming is TX, outgoing is RX.
 * For virtualisers, incoming is RX, outgoing is TX. */
// Store macs contiguously for better cache performance during lookup.
// Since all MACs not on our internal MAC->port mapping are not ours, we don't need the mapping
// If we want to dynamically add/remove allowed connections, we will just update the allowlist
// TODO: better allow or deny in principle?

typedef struct vswitch_state {
    // Queues for clients
    net_queue_handle_t rx_queues_clients[SDDF_NET_MAX_CLIENTS];
    net_queue_handle_t tx_queues_clients[SDDF_NET_MAX_CLIENTS];
    // Queues for the virt
    net_queue_handle_t rx_queue_virt;
    net_queue_handle_t tx_queue_virt;

    vswitch_port_bitmap_t allow_list[SDDF_NET_MAX_CLIENTS]; // TODO: should it be denylist instead?
} vswitch_state_t;

static vswitch_state_t state;

static int channel_map_find(channel_map_t *map, const uint8_t *dest_macaddr)
{
    for (int i = 0; i < map->len; i++) {
        if (mac802_addr_eq(map->macs[i].addr, dest_macaddr)) {
            return map->port[i];
        }
    }
    return UNKNOWN_PORT;
}

static bool channel_map_add(channel_map_t *map, const uint8_t *macaddr, int port)
{
    if (map->len >= VSWITCH_LOOKUP_SIZE) {
        sddf_dprintf("VSWITCH: Channel map is full\n");
        return false;
    }
    if (channel_map_find(map, macaddr) != UNKNOWN_PORT) {
        return false;
    }
    if (mac802_addr_is_bcast(macaddr)) {
        return false;
    }

    sddf_memcpy(map->macs[map->len].addr, macaddr, 6);
    map->port[map->len] = port;
    map->len++;
    return true;
}

static void forward_frame(vswitch_channel_t *src, vswitch_channel_t *dest, net_buff_desc_t *src_buf)
{
    const char *src_data = src->data_region + src_buf->io_or_offset;

    net_buff_desc_t d_buffer;
    if (net_dequeue_free(&dest->q, &d_buffer) != 0) {
        return;
    }
    // TODO: make fast memcpy
    sddf_memcpy(dest->data_region + d_buffer.io_or_offset, src_data, src_buf->len);

    d_buffer.len = src_buf->len;
    net_enqueue_active(&dest->q, d_buffer);

    if (net_require_signal_active(&dest->q)) {
        net_cancel_signal_active(&dest->q);
        microkit_notify(dest->ch);
    }
}

static void try_broadcast(int src_port, vswitch_port_t *src, net_buff_desc_t *buffer)
{
    for (int i = 0; i < VSWITCH_PORT_COUNT; i++) {
        if (i != src_port && vswitch_can_send_to(src, i)) {
            vswitch_channel_t *outgoing = &vswitch.ports[i].outgoing;
            forward_frame(&src->incoming, outgoing, buffer);
        }
    }
}

static void try_send(vswitch_port_t *src, const uint8_t *dest_macaddr, net_buff_desc_t *buffer)
{
    int dest_port = channel_map_find(&vswitch.map, dest_macaddr);

    if (dest_port == UNKNOWN_PORT || !vswitch_can_send_to(src, dest_port)) {
        return;
    }

    vswitch_channel_t *outgoing = &vswitch.ports[dest_port].outgoing;
    forward_frame(&src->incoming, outgoing, buffer);
}

static void notified_by_port(int port)
{
    net_buff_desc_t sddf_buffer;

    vswitch_port_t *src = &vswitch.ports[port];
    net_queue_handle_t *src_queue = &src->incoming.q;

    bool reprocess = true;
    while (reprocess) {
        while (net_dequeue_active(src_queue, &sddf_buffer) != -1) {
            const char *frame_data = src->incoming.data_region + sddf_buffer.io_or_offset;
            const struct ether_addr *macaddr = (void *)frame_data;

            // Add forwarding table entry from source MAC to port
            channel_map_add(&vswitch.map, macaddr->ether_src_addr_octet, port);

            // Forward frame
            if (mac802_addr_is_bcast(macaddr->ether_dest_addr_octet)) {
                try_broadcast(port, src, &sddf_buffer);
            } else {
                try_send(src, macaddr->ether_dest_addr_octet, &sddf_buffer);
            }

            sddf_buffer.len = 0;
            net_enqueue_free(src_queue, sddf_buffer);
        }

        net_request_signal_active(src_queue);
        reprocess = false;

        if (!net_queue_empty_active(src_queue)) {
            net_cancel_signal_active(src_queue);
            reprocess = true;
        }
    }
}

void notified(microkit_channel ch)
{



    // This could be optimised but port count is usually low.
    for (int port = 0; port < VSWITCH_PORT_COUNT; port++) {
        if (ch == vswitch.ports[port].incoming.ch) {
            notified_by_port(port);
            return;
        }
        if (ch == vswitch.ports[port].outgoing.ch) {
            // TODO: check if anyone is waiting for room in this port?
            // Might be better to drop packets in this case.
            return;
        }
    }
}

void init(void)
{
    assert(net_config_check_magic(&config));

    /* Set up client queues and buffers for copying? */
    uint8_t num_clients = config.num_clients;
    for (int i = 0; i < num_clients; i++) {
        net_queue_init(&state.rx_queues_clients[i], config.clients_rx[i].free_queue.vaddr, config.clients_rx[i].active_queue.vaddr,
                       config.clients_rx[i].num_buffers);
        net_queue_init(&state.tx_queues_clients[i], config.clients_tx[i].free_queue.vaddr, config.clients_tx[i].active_queue.vaddr,
                       config.clients_tx[i].num_buffers);
        net_buffers_init(&state.rx_queues_clients[i], 0); // TODO: should the offset be set?
        net_buffers_init(&state.tx_queues_clients[i], 0);
    }

    /* Set virt queues */
    net_queue_init(&state.rx_queue_virt, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);
    net_queue_init(&state.tx_queue_virt, config.virt_tx.free_queue.vaddr, config.virt_tx.active_queue.vaddr,
                   config.virt_tx.num_buffers);

    // Seed the allow_list based on predefined settings */
}
