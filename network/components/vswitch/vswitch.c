/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

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
#define VSWITCH_IMPL
#include <vswitch_config.h>

_Static_assert(VSWITCH_PORT_COUNT <= VSWITCH_MAX_PORT_COUNT, "Too many ports");
#define UNKNOWN_PORT -1

typedef struct mac_addr {
    uint8_t addr[6];
} mac_addr_t;

typedef struct channel_map {
    // Store macs contiguously for better cache performance during lookup.
    mac_addr_t macs[VSWITCH_LOOKUP_SIZE];
    uint8_t port[VSWITCH_LOOKUP_SIZE];
    uint32_t len;
} channel_map_t;

static struct {
    vswitch_port_t ports[VSWITCH_PORT_COUNT];
    channel_map_t map;
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

static int channel_map_find(channel_map_t *map, uint8_t *dest_macaddr)
{
    for (int i = 0; i < map->len; i++) {
        if (mac802_addr_eq(map->macs[i].addr, dest_macaddr)) {
            return map->port[i];
        }
    }
    return UNKNOWN_PORT;
}

static bool channel_map_add(channel_map_t *map, uint8_t *macaddr, int port)
{
    if (map->len >= VSWITCH_LOOKUP_SIZE) {
        sddf_dprintf("VSWITCH: Channel map is full\n");
        return false;
    }
    if (channel_map_find(map, macaddr) != UNKNOWN_PORT) {
        return false;
    }
    if (mac802_addr_eq(macaddr, bcast_macaddr)) {
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

static void try_send(vswitch_port_t *src, uint8_t *dest_macaddr, net_buff_desc_t *buffer)
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
            char *frame_data = src->incoming.data_region + sddf_buffer.io_or_offset;

            struct ether_addr *macaddr = (struct ether_addr *)frame_data;

            // Add forwarding table entry from source MAC to port
            channel_map_add(&vswitch.map, macaddr->ether_src_addr_octet, port);

            // Forward frame
            if (mac802_addr_eq(macaddr->ether_dest_addr_octet, bcast_macaddr)) {
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
    for (int i = 0; i < VSWITCH_PORT_COUNT; i++)
    {
        net_vswitch_init_port(i, &vswitch.ports[i]);
        net_buffers_init(&vswitch.ports[i].outgoing.q, 0);
    }
}
