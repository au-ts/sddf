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

#define VSWITCH_VIRT_PORT (SDDF_NET_MAX_CLIENTS - 1)

#define NUM_BUFFERS (512)

__attribute__((__section__(".net_vswitch_config"))) net_vswitch_config_t config;

typedef struct vswitch_state {
    /* Rx/Tx swapped for the virtualizer in the system file */
    net_queue_handle_t rx_queues[SDDF_NET_MAX_CLIENTS];
    net_queue_handle_t tx_queues[SDDF_NET_MAX_CLIENTS];
    uint64_t allow_list[SDDF_NET_MAX_CLIENTS];
} vswitch_state_t;

static vswitch_state_t state;

uint32_t *buffer_refs;

static bool forward_frame(net_vswitch_port_config_t *src, net_vswitch_port_config_t *dst, net_buff_desc_t *src_buf)
{
    net_buff_desc_t d_buffer;

    d_buffer.len = src_buf->len;
    d_buffer.io_or_offset = src_buf->io_or_offset;
    /* tag the owner of this buffer so we know which reference slot increment */
    d_buffer.oid = src->id;
    net_enqueue_active(&state.rx_queues[dst->id], d_buffer);

    /* mark that this buffer has been passed once */
    int ref_index = src_buf->io_or_offset / NET_BUFFER_SIZE;
    buffer_refs[src->id * NUM_BUFFERS + ref_index]++;

    if (net_require_signal_active(&state.rx_queues[dst->id])) {
        net_cancel_signal_active(&state.rx_queues[dst->id]);
        sddf_notify(dst->rx.id);
        return true;
    }
    return false;
}

static bool vswitch_can_send_to(int src_id, int dst_id)
{
    return state.allow_list[src_id] & ((uint64_t)1 << dst_id);
}

int mac_addr_find(const uint8_t *dest_macaddr)
{
    mac_addr_t *mac;
    /* try matching each MAC in the list (skip ID SDDF_NET_MAX_CLIENTS - 1) - virts */
    for (int i = 0; i < VSWITCH_VIRT_PORT; i++) {
        for (int j = 0; j < TEMP_MAX_MACS_PER_CLIENT; j++) {
            mac = &config.ports[i].mac_addrs[j];
            if (mac802_addr_eq(mac->addr, dest_macaddr)) {
                return i; // this is the ID of the client we matched
            }
        }
    }
    /* I tried so hard and got so far, and in the end it doesn't even matter - default to forward to external port */
    return VSWITCH_VIRT_PORT;
}

static bool try_broadcast(net_vswitch_port_config_t *src, net_buff_desc_t *buffer)
{
    // just need one success to not drop?
    bool success = false;
    /* Only broadcast to allowed, exclude myself */
    for (int i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        if (config.ports[i].connected && i != src->id && vswitch_can_send_to(src->id, config.ports[i].id)) {
            success = forward_frame(src, &config.ports[i], buffer);
            sddf_printf_("VSWITCH Success of bcast id: %d is %d\n", i, success);
        }
    }
    return success;
}

static bool try_send(net_vswitch_port_config_t *src, const uint8_t *dest_macaddr, net_buff_desc_t *buffer)
{
    bool success = false;
    int dst_id = mac_addr_find(dest_macaddr);

    if (vswitch_can_send_to(src->id, dst_id)) {
        /* at least one of them succeeded */
        if (forward_frame(src, &config.ports[dst_id], buffer))
            success = true;
    }
    return success;
}

/* Read free buffers from RX, see if the refcount is 0, and then return them to TX and notify the TX clients */
static void rx_return(net_vswitch_port_config_t *port)
{
    bool signal_tx = false;
    net_queue_handle_t *src = &state.rx_queues[port->id];
    net_queue_handle_t *dst;

    bool reprocess = true;
    while (reprocess) {
        while (!net_queue_empty_free(src)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(src, &buffer);
            assert(!err);

            int ref_index = buffer.io_or_offset / NET_BUFFER_SIZE;
            assert(buffer_refs[buffer.oid * NUM_BUFFERS + ref_index] != 0);

            buffer_refs[buffer.oid * NUM_BUFFERS + ref_index]--;

            if (buffer_refs[buffer.oid * NUM_BUFFERS + ref_index] != 0) {
                continue;
            }

            /* return the buffer to its owner */
            dst = &state.tx_queues[buffer.oid];
            err = net_enqueue_free(dst, buffer);
            assert(!err);

            signal_tx = true;
            //net_request_signal_free(dst); TODO: is this necessary?
            if (signal_tx && net_require_signal_free(dst)) {
                net_cancel_signal_free(dst);
                sddf_deferred_notify(config.ports[buffer.oid].tx.id); // TODO: deferred?
            }
        }

        net_request_signal_free(src);
        reprocess = false;

        if (!net_queue_empty_free(src)) {
            net_cancel_signal_free(src);
            reprocess = true;
        }
    }
}

static void forward_traffic_from(net_vswitch_port_config_t *port)
{
    /* Read from TX and fill in the corresponding RX (switched for virtualizer but we handle that in SDF) */
    net_queue_handle_t *src = &state.tx_queues[port->id];

    bool reprocess = true;
    while (reprocess) {
        while (!net_queue_empty_active(src)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(src, &buffer);
            assert(!err);

            const char *frame_data = port->tx_data.region.vaddr + buffer.io_or_offset;
            const struct ether_addr *macaddr = (void *)frame_data;
            bool transmitted = false;

            if (mac802_addr_is_bcast(macaddr->ether_dest_addr_octet)) {
                transmitted = try_broadcast(port, &buffer);
            } else {
                transmitted = try_send(port, macaddr->ether_dest_addr_octet, &buffer);
            }

            if (!transmitted) {
                net_enqueue_free(src, buffer);
                net_request_signal_free(src);
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
    for (int i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        if (!config.ports[i].connected)
            continue;
        if (ch == config.ports[i].tx.id) {
            forward_traffic_from(&config.ports[i]);
            break;
        } else if (ch == config.ports[i].rx.id) {
            rx_return(&config.ports[i]);
            break;
        }
    }
}

void init(void)
{
    assert(net_config_check_magic(&config));

    buffer_refs = config.buffer_metadata.vaddr;

    /* Set up client queues and buffers for copying? */
    for (int i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        if (!config.ports[i].connected)
            continue;
        net_queue_init(&state.rx_queues[i], config.ports[i].rx.free_queue.vaddr, config.ports[i].rx.active_queue.vaddr,
                       config.ports[i].rx.num_buffers);
        net_queue_init(&state.tx_queues[i], config.ports[i].tx.free_queue.vaddr, config.ports[i].tx.active_queue.vaddr,
                       config.ports[i].tx.num_buffers);

        /* Seed the allow_list based on predefined settings */
        // for now quick hack, send all to all
        state.allow_list[i] = UINT64_MAX; // TODO: later construct properly
    }
    //state.allow_list[0] = ((uint64_t)0x1 << 63 | (uint64_t)0x1 << 2); // Client 0 can send only to out and to client 2
}
