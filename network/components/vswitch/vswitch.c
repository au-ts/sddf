/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/network/mac802.h>
#include <sddf/network/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

// #include "ethernet.h"
#include "layout.h"

// A vswitch consists of a number of ports, each with an incoming and outgoing
// set of channels & queues. These ports are analogous to the ports on a
// physical switch.

// TODO: move to config header
#define VSWITCH_PORT_COUNT 4
#define VSWITCH_LOOKUP_SIZE 256

typedef struct mac_addr {
    uint8_t addr[6];
} mac_addr_t;

typedef struct channel_map {
    // Store macs contiguously for better cache performance during lookup.
    mac_addr_t macs[VSWITCH_LOOKUP_SIZE];
    uint8_t port[VSWITCH_LOOKUP_SIZE];
    uint32_t len;
} channel_map_t;

typedef struct channel {
    net_queue_handle_t q;
    size_t ch;
    char *data_region;
} channel_t;

typedef struct port {
    // For clients, incoming is TX, outgoing is RX
    // For virtualisers, incoming is RX, outgoing is TX
    channel_t incoming;
    channel_t outgoing;
} port_t;

static struct {
    port_t ports[VSWITCH_PORT_COUNT];
    channel_map_t map;
    // TODO: add port communication filter
} vswitch;


static void debug_dump_packet(int len, uint8_t *buffer)
{
    struct ether_addr *macaddr = (struct ether_addr *)buffer;
    sddf_dprintf("VIRTIO(NET)|DUMP PACKET:\n");
    sddf_dprintf("dest MAC: "PR_MAC802_ADDR", src MAC: "PR_MAC802_ADDR", type: 0x%02x%02x, size: %d\n",
            PR_MAC802_DEST_ADDR_ARGS(macaddr), PR_MAC802_SRC_ADDR_ARGS(macaddr),
            macaddr->etype[0], macaddr->etype[1], len);
    sddf_dprintf("-------------------- payload begin --------------------\n");
    for (int i = 0; i < len; i++) {
        sddf_dprintf("%02x ", macaddr->payload[i]);
    }
    sddf_dprintf("\n");
    sddf_dprintf("--------------------- payload end ---------------------\n");
    sddf_dprintf("\n");
}

static int find_dest_port(channel_map_t *map, uint8_t *dest_macaddr)
{
    for (int i = 0; i < map->len; i++) {
        if (mac802_addr_eq(map->macs[i].addr, dest_macaddr)) {
            return map->port[i];
        }
    }
    return -1;
}

static bool forward_frame(channel_t *src, channel_t *dest, net_buff_desc_t *src_buf)
{
    char *src_data = src->data_region + src_buf->io_or_offset;

    net_buff_desc_t d_buffer;
    if (net_dequeue_free(&dest->q, &d_buffer) != 0) {
        return false;
    }
    // TODO: make fast memcpy
    sddf_memcpy(dest->data_region + d_buffer.io_or_offset, src_data, src_buf->len);

    d_buffer.len = src_buf->len;
    net_enqueue_active(&dest->q, d_buffer);

    return true;
}

static void notified_by_port(int port)
{
    net_buff_desc_t sddf_buffer;
    port_t *p = &vswitch.ports[port];

    channel_t *incoming = &p->incoming;
    net_queue_handle_t *src_queue = &incoming->q;

    bool reprocess = true;
    while (reprocess) {
        while (net_dequeue_active(src_queue, &sddf_buffer) != -1) {
            struct ether_addr *macaddr = (struct ether_addr *)sddf_buffer.io_or_offset;
            int dest_port = find_dest_port(&vswitch.map, macaddr->ether_dest_addr_octet);

            if (dest_port < 0) {
                // Bad destination, drop packet
                continue;
            }

            // TODO: check that src is allowed to send to dest
            channel_t *outgoing = &vswitch.ports[dest_port].outgoing;

            bool notify = forward_frame(incoming, outgoing, &sddf_buffer);

            if (notify && net_require_signal_active(&outgoing->q)) {
                net_cancel_signal_active(&outgoing->q);
                if (!have_signal) {
                    microkit_notify_delayed(outgoing->ch);
                } else if (signal_cap != BASE_OUTPUT_NOTIFICATION_CAP + outgoing->ch) {
                    microkit_notify(outgoing->ch);
                }
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

// @jade: this function should contain all the hard-coded craps, so it will be
// easier to refactor later.
void init(void)
{
    // @jade: should we initialize all the queues or 
    // should the clients initialize their own queues?

    // client #0
    net_queue_init(&clients[0].tx_queue, (net_queue_t *)tx_free_cli0,
                   (net_queue_t *)tx_active_cli0, TX_QUEUE_SIZE_DRIV);
    clients[0].tx_ch = TX_CLI0_CH;

    net_queue_init(&clients[0].rx_queue, (net_queue_t *)rx_free_cli0,
                   (net_queue_t *)rx_active_cli0, RX_QUEUE_SIZE_DRIV);
    clients[0].rx_ch = RX_CLI0_CH;

    // @jade: how do I tell clients their mac addresses?
    mac802_addr_cp(vswitch_mac_base, clients[0].mac_addr, 0);

    // client #1
    net_queue_init(&clients[1].tx_queue, (net_queue_t *)tx_free_cli1,
                   (net_queue_t *)tx_active_cli1, TX_QUEUE_SIZE_DRIV);
    clients[1].tx_ch = TX_CLI1_CH;

    net_queue_init(&clients[1].rx_queue, (net_queue_t *)rx_free_cli1,
                   (net_queue_t *)rx_active_cli1, RX_QUEUE_SIZE_DRIV);
    clients[1].rx_ch = RX_CLI1_CH;

    mac802_addr_cp(vswitch_mac_base, clients[1].mac_addr, 1);
}
