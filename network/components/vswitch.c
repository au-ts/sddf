/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "os/sddf.h"
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

__attribute__((__section__(".net_vswitch_config"))) net_vswitch_config_t config;

typedef struct vswitch_state {
    /* Rx/Tx swapped for the virtualizer */ // TODO: is that truly true? I am not 100% sure yet
    net_queue_handle_t rx_queues[SDDF_NET_MAX_CLIENTS];
    net_queue_handle_t tx_queues[SDDF_NET_MAX_CLIENTS];
    uint64_t allow_list[SDDF_NET_MAX_CLIENTS];
} vswitch_state_t;

static vswitch_state_t state;

uint32_t **buffer_refs;

// TODO: do the buffer incremeting here, let's keep things localised
static void forward_frame(net_vswitch_port_config_t *src, net_vswitch_port_config_t *dst, net_buff_desc_t *src_buf)
{
    const char *src_data = src->tx_data.vaddr + src_buf->io_or_offset;

    net_buff_desc_t d_buffer;
    if (net_dequeue_free(&state.rx_queues[dst->id], &d_buffer) != 0) {
        return;
    }

    d_buffer.len = src_buf->len;
    d_buffer.io_or_offset = src_buf->io_or_offset;
    d_buffer.oid = src->id; // tag the owner of this buffer so we know which reference slot increment
    net_enqueue_active(&state.rx_queues[dst->id], d_buffer);

    // TODO: recheck if my logic is not funky here - offsets etc
    // mark that this buffer has been passed once
    int ref_index = src_buf->io_or_offset / NET_BUFFER_SIZE;
    buffer_refs[src->id][ref_index]++;

    if (net_require_signal_active(&state.rx_queues[dst->id])) {
        net_cancel_signal_active(&state.rx_queues[dst->id]);
        sddf_notify(dst->rx.id);
    }
}

static bool vswitch_can_send_to(int src_id, int dst_id)
{
    return state.allow_list[src_id] & (1 << (uint64_t)dst_id);
}

int mac_addr_find(const uint8_t *dest_macaddr) {
    mac_addr_t *mac;
    // try matching each MAC in the list (skip ID 0)
    for (int i = 1; i < SDDF_NET_MAX_CLIENTS; i++) { // TODO: can we simplify that loop?
        for (int j = 0; j < TEMP_MAX_MACS_PER_CLIENT; j++) {
            mac = &config.ports[i].mac_addrs[j];
            if (mac802_addr_eq(mac->addr, dest_macaddr)) {
                return i; // this is the ID of the client we matched
            }
        }
    }
    // I tried so hard and got so far, and in the end it doesn't even matter - default to forward to external port
    return 0;
}

static void try_broadcast(net_vswitch_port_config_t *src, net_buff_desc_t *buffer)
{
    // Only broadcast to allowed
    for (int i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        if (i != src->id && vswitch_can_send_to(src->id, config.ports[i].id)) {
            forward_frame(src, &config.ports[i], buffer);
        }
    }
}

static void try_send(net_vswitch_port_config_t *src, const uint8_t *dest_macaddr, net_buff_desc_t *buffer)
{
    int dst_id = mac_addr_find(dest_macaddr);

    if (vswitch_can_send_to(src->id, dst_id)) {
        forward_frame(src, &config.ports[dst_id], buffer);
    } else {
        // drop the packet
        // TODO: impl, do we have to do anything here?
        return;
    }
}

static void rx_provide()
{
    // TODO: not sure if I have to handle that like it is handled in rx_virt?
    uint64_t notifications = 0;
    // Return empty buffers
    for (int i = 0; i < config.num_ports; i++) {
        bool reprocess = true;
        net_queue_handle_t *src = &state.rx_queues[i];
        while (reprocess) {
            while (!net_queue_empty_free(src)) {
                net_buff_desc_t buffer;
                int err = net_dequeue_free(src, &buffer);
                assert(!err);
                // TODO: handle if we need to handle the offsets etc in any special way
                int ref_index = buffer.io_or_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[buffer.oid][ref_index] != 0);

                buffer_refs[buffer.oid][ref_index]--;

                if (buffer_refs[buffer.oid][ref_index] != 0) {
                    continue;
                }

                // return the buffer to its owner
                // TODO: should I handle the offsets like virt does?
                net_queue_handle_t *dst = &state.rx_queues[buffer.oid];
                err = net_enqueue_free(dst, buffer);
                assert(!err);
                notifications |= (1 << buffer.oid);
            }

            net_request_signal_free(src);
            reprocess = false;

            if (!net_queue_empty_free(src)) {
                net_cancel_signal_free(src);
                reprocess = true;
            }
        }
    }

    // Notify every owner
    for (int i = 0; i < config.num_ports; i++) {
        if (notifications & (1 << i) && net_require_signal_free(&state.rx_queues[i])) {
            net_cancel_signal_free(&state.rx_queues[i]);
            sddf_deferred_notify(config.ports[i].id);
        }
    }
}

static void forward_traffic_from(net_vswitch_port_config_t *port)
{
    // Here we read from TX and fill in the corresponding RX (switched for virtualizer but we handle that in SDF)
    // TODO: Think if we don't need to do some other handling for virt, should be fine
    net_queue_handle_t *src = &state.tx_queues[port->id];

    bool reprocess = true;
    while (reprocess) {
        // read from active queue
        while (!net_queue_empty_active(src)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(src, &buffer);
            assert(!err);

            const char *frame_data = port->tx_data.vaddr + buffer.io_or_offset;
            const struct ether_addr *macaddr = (void *)frame_data;
            // find the receiver(s)
            // Forward frame
            // queue packets for the receivers (inside forward_frame)
            if (mac802_addr_is_bcast(macaddr->ether_dest_addr_octet)) {
                try_broadcast(port, &buffer);
            } else {
                try_send(port, macaddr->ether_dest_addr_octet, &buffer);
            }

            // We do not return the buffers here
            //buffer.len = 0;
            //net_enqueue_free(src, buffer);
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
    for (int i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        if (ch == config.ports[i].rx.id) {
            forward_traffic_from(&config.ports[i]);
            break;
        }
    }
    rx_provide();
}

void init(void)
{
    assert(net_config_check_magic(&config));

    buffer_refs = config.buffer_metadata.vaddr;

    /* Set up client queues and buffers for copying? */
    for (int i = 0; i < config.num_ports; i++) {
        net_queue_init(&state.rx_queues[i], config.ports[i].rx.free_queue.vaddr, config.ports[i].rx.active_queue.vaddr,
                       config.ports[i].rx.num_buffers);
        net_queue_init(&state.tx_queues[i], config.ports[i].tx.free_queue.vaddr, config.ports[i].tx.active_queue.vaddr,
                       config.ports[i].tx.num_buffers);
        net_buffers_init(&state.rx_queues[i], 0); // TODO: should the offset be set? - probably not because this is device-only offset
    }

    /* Seed the allow_list based on predefined settings */
    // for now quick hack, send all to all
    for (int i = 0; i < config.num_ports; i++)
        state.allow_list[i] = UINT64_MAX;
}
