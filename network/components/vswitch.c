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
} vswitch_state_t;

static vswitch_state_t state;

bool need_rx_signal[SDDF_NET_MAX_CLIENTS];
bool need_tx_signal[SDDF_NET_MAX_CLIENTS];

uint8_t *buffer_refs;

static bool forward_frame(uint8_t src_id, uint8_t dst_id, net_buff_desc_t *src_buf)
{
    net_buff_desc_t d_buffer;

    d_buffer.len = src_buf->len;
    d_buffer.io_or_offset = src_buf->io_or_offset;
    /* Add a tag for the owner of this buffer so vswitch knows which reference slot to increment
     * Also, the copier will use this tag to know which buffer to address */
    d_buffer.oid = src_id;

    /* Drop if the dest queue is full */
    if (!net_queue_full_active(&state.rx_queues[dst_id])) {
        net_enqueue_active(&state.rx_queues[dst_id], d_buffer);
    } else {
        return false;
    }

    /* Mark that this buffer has been passed once */
    int ref_index = src_buf->io_or_offset / NET_BUFFER_SIZE;
    buffer_refs[src_id * config.buffers_per_client + ref_index]++;

    if (net_require_signal_active(&state.rx_queues[dst_id])) { // TODO: is that not a failure?
        need_rx_signal[dst_id] = true;
        return true;
    }

    /* Failed to enqueue, decrement the ref */
    buffer_refs[src_id * config.buffers_per_client + ref_index]--;
    return false;
}

static bool vswitch_can_send_to(uint8_t src_id, uint8_t dst_id)
{
    return state.allow_list[src_id] & ((uint64_t)1 << dst_id);
}

int mac_addr_find(const mac_addr_t *dest_macaddr)
{
    mac_addr_t *mac;
    /* Try matching each MAC in the list (skip VSWITCH_VIRT_PORT) - virts */
    for (uint8_t i = 0; i < config.num_ports; i++) {
        mac = &config.ports[i].mac_addr;
        if (mac802_addr_eq(mac->addr, dest_macaddr->addr)) {
            return i;
        }
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
            success |= forward_frame(src_id, i, buffer);
        }
    }
    return success;
}

static bool try_send(uint8_t src_id, const mac_addr_t *dest_macaddr, net_buff_desc_t *buffer)
{
    bool success = false;
    uint8_t dst_id = mac_addr_find(dest_macaddr);

    if (vswitch_can_send_to(src_id, dst_id)) {
        /* At least one of them succeeded */
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
            assert(buffer_refs[buffer.oid * config.buffers_per_client + ref_index] != 0);

            buffer_refs[buffer.oid * config.buffers_per_client + ref_index]--;

            if (buffer_refs[buffer.oid * config.buffers_per_client + ref_index] != 0) {
                continue;
            }

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
                || buffer.io_or_offset >= NET_BUFFER_SIZE * config.buffers_per_client * config.num_ports) { // TODO: not sure that this is not too optimistic
                sddf_dprintf("VSWITCH|LOG: Port provided offset %lx which is not buffer aligned or outside of buffer region\n",
                             buffer.io_or_offset);
                err = net_enqueue_free(src, buffer);
                assert(!err);
                continue;
            }

            if (buffer.oid > config.num_ports) {
                sddf_dprintf("VSWITCH|LOG: Port provided buffer with id %d which is not from within the mapped memory\n",
                             buffer.oid);
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
        need_rx_signal[i] = false;
        need_tx_signal[i] = false;
    }

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
            sddf_notify(config.ports[i].rx.id);
        }
        if (need_tx_signal[i] && net_require_signal_free(&state.tx_queues[i])) {
            net_cancel_signal_free(&state.tx_queues[i]);
            sddf_notify(config.ports[i].tx.id);
        }
    }
}

void init(void)
{
    assert(net_config_check_magic(&config));

    buffer_refs = config.buffer_metadata.vaddr;

    /* Set up client queues and buffers for copying? */
    for (uint8_t i = 0; i <= config.num_ports; i++) {
        net_queue_init(&state.rx_queues[i], config.ports[i].rx.free_queue.vaddr, config.ports[i].rx.active_queue.vaddr,
                       config.ports[i].rx.num_buffers);
        net_queue_init(&state.tx_queues[i], config.ports[i].tx.free_queue.vaddr, config.ports[i].tx.active_queue.vaddr,
                       config.ports[i].tx.num_buffers);

        /* Seed the allow_list based on predefined settings */
        state.allow_list[i] = config.ports[i].acl;
    }
    //state.allow_list[0] = 13;
    //state.allow_list[1] = 15;
    //state.allow_list[2] = 15;
    //state.allow_list[3] = 15;
    //state.allow_list[0] = ((uint64_t)0x1 << 63 | (uint64_t)0x1 << 2); // Client 0 can send only to out and to client 2
}
