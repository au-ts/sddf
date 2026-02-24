/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "sddf/network/config.h"
#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/network/mac802.h>
#include <sddf/network/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#define UNKNOWN_CID -1

__attribute__((__section__(".net_vswitch_config"))) net_vswitch_config_t config;

typedef struct vswitch_state {
    // Queues for clients
    net_queue_handle_t rx_copy_queues_clients[SDDF_NET_MAX_CLIENTS];
    net_queue_handle_t tx_queues_clients[SDDF_NET_MAX_CLIENTS];
    // Queues for the virt
    net_queue_handle_t rx_queue_virt;
    net_queue_handle_t tx_queue_virt;

    vswitch_port_bitmap_t allow_list[SDDF_NET_MAX_CLIENTS];
} vswitch_state_t;

static vswitch_state_t state;

static void forward_frame(int src_cid, int dst_cid, net_buff_desc_t *src_buf)
{
    // 2 cases here - src_cid is virt or a client, can we already commonalize that?
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

static bool vswitch_can_send_to(int src_cid, int dst_cid) {
    return config.clients[src_cid].allow_list & (1 << (uint64_t)dst_cid);
}

int mac_addr_find(const uint8_t *dest_macaddr) {
    mac_addr_t *client_mac;
    // try matching each MAC in the list
    for (int i = 0; i < SDDF_NET_MAX_CLIENTS; i++) { // TODO: can we simplify that loop?
        for (int j = 0; j < TEMP_MAX_MACS_PER_CLIENT; j++) {
            client_mac = &config.clients[i].mac_addrs[j];
            if (mac802_addr_eq(client_mac->addr, dest_macaddr)) {
                return i; // this is the ID of the client we matched
            }
        }
    }
    // I tried so hard and got so far, and in the end it doesn't even matter
    return UNKNOWN_CID;
}

static void try_broadcast(uint8_t src_cid, net_buff_desc_t *buffer)
{
    // Only broadcast to allowed
    //for (int i = 0; i < VSWITCH_PORT_COUNT; i++) {
    //    if (i != src_port && vswitch_can_send_to(src, i)) {
    //        vswitch_channel_t *outgoing = &vswitch.ports[i].outgoing;
    //        forward_frame(&src->incoming, outgoing, buffer);
    //    }
    //}
}

static void try_send(uint8_t src_cid, const uint8_t *dest_macaddr, net_buff_desc_t *buffer)
{
    int dest_cid = mac_addr_find(dest_macaddr);

    // we don't know this CID - forward via virts
    if (dest_cid == UNKNOWN_CID) {

    } else if (!vswitch_can_send_to((int)src_cid, dest_cid)) {
        // we have to drop this packet - allow_list disallows
        return;
    }

    forward_frame(src_cid, dest_cid, buffer);
}

//static void notified_by_port(int port)
//{
//    net_buff_desc_t sddf_buffer;
//
//    vswitch_port_t *src = &vswitch.ports[port];
//    net_queue_handle_t *src_queue = &src->incoming.q;
//
//    bool reprocess = true;
//    while (reprocess) {
//        while (net_dequeue_active(src_queue, &sddf_buffer) != -1) {
//            const char *frame_data = src->incoming.data_region + sddf_buffer.io_or_offset;
//            const struct ether_addr *macaddr = (void *)frame_data;
//
//            // Add forwarding table entry from source MAC to port
//            channel_map_add(&vswitch.map, macaddr->ether_src_addr_octet, port);
//
//            // Forward frame
//            if (mac802_addr_is_bcast(macaddr->ether_dest_addr_octet)) {
//                try_broadcast(port, src, &buffer);
//            } else {
//                try_send(src, macaddr->ether_dest_addr_octet, &sddf_buffer);
//            }
//
//            sddf_buffer.len = 0;
//            net_enqueue_free(src_queue, sddf_buffer);
//        }
//
//        net_request_signal_active(src_queue);
//        reprocess = false;
//
//        if (!net_queue_empty_active()) {
//            net_cancel_signal_active(src_queue);
//            reprocess = true;
//        }
//    }
//}

// TODO: honestly, think if we need the split between client/virt - this doubles a lot of effort.
static void forward_traffic_from_virt() {
    //bool reprocess = true;

    //while (reprocess) {
    //    while (net_dequeue_active(net_queue_handle_t *queue, net_buff_desc_t *buffer)

    //}
}

static void forward_traffic_from_client(uint8_t cid) {
    net_queue_handle_t *src = &state.rx_copy_queues_clients[cid];

    bool reprocess = true;
    while (reprocess) {
        // read from active queue
        while (!net_queue_empty_active(src)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(src, &buffer);
            assert(!err);

            const char *frame_data = config.clients[cid].tx_data.vaddr + buffer.io_or_offset;
            const struct ether_addr *macaddr = (void *)frame_data;
            // find the receiver(s)
            // Forward frame
            // queue packets for the receivers (inside forward_frame)
            if (mac802_addr_is_bcast(macaddr->ether_dest_addr_octet)) {
                try_broadcast(cid, &buffer);
            } else {
                try_send(cid, macaddr->ether_dest_addr_octet, &buffer);
            }

            // return the buffers
            buffer.len = 0;
            net_enqueue_free(src, buffer);
        }

        net_request_signal_active(src);
        reprocess = false;

        if (!net_queue_empty_active(src)) {
            net_cancel_signal_active(src);
            reprocess = true;
        }
    }
}

void notified(microkit_channel_t ch)
{
    // TODO: smartly find out which ch corresponds to what client?
    // upon notification, forward the packet to corresponding client

    if (ch == config.virt_rx.id) {
        // TODO: do we need a special case for this?
        forward_traffic_from_virt(ch);
    } else {
        // TODO: we assume client assumes it's PD's ID - need to be enforced - or we have to create additional mapping of CLient ID -> idx in the array
        for (int cid = 0; cid < SDDF_NET_MAX_CLIENTS; cid++) {
            if (ch == config.clients[cid].copy_rx.id) {
                forward_traffic_from_client(cid);
                return;
            }
        }
        sddf_dprintf("FAILED TO MATCH\n");
        // not for us? error?
        return;
    }
}

void init(void)
{
    assert(net_config_check_magic(&config));

    /* Set up client queues and buffers for copying? */
    uint8_t num_clients = config.num_clients;
    for (int i = 0; i < num_clients; i++) {
        net_queue_init(&state.rx_copy_queues_clients[i], config.clients[i].copy_rx.free_queue.vaddr, config.clients[i].copy_rx.active_queue.vaddr,
                       config.clients[i].copy_rx.num_buffers);
        net_queue_init(&state.tx_queues_clients[i], config.clients[i].tx.free_queue.vaddr, config.clients[i].tx.active_queue.vaddr,
                       config.clients[i].tx.num_buffers);
        net_buffers_init(&state.rx_copy_queues_clients[i], 0); // TODO: should the offset be set? - probably not because this is device-only offset
    }

    /* Set virt queues */
    net_queue_init(&state.rx_queue_virt, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);
    net_queue_init(&state.tx_queue_virt, config.virt_tx.free_queue.vaddr, config.virt_tx.active_queue.vaddr,
                   config.virt_tx.num_buffers);
    net_buffers_init(&state.rx_queue_virt, 0);

    // Seed the allow_list based on predefined settings */
}
