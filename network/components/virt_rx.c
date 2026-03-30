/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/network/constants.h>
#include <sddf/network/queue.h>
#include <sddf/network/util.h>
#include <sddf/network/config.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/util/cache.h>

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
  is a broadcast address. */
int get_mac_addr_match(struct ethernet_header *buffer)
{
    for (int client = 0; client < config.num_clients; client++) {
        bool match = true;
        for (int i = 0; (i < ETH_HWADDR_LEN) && match; i++) {
            if (buffer->dest.addr[i] != config.clients[client].mac_addr[i]) {
                match = false;
            }
        }
        if (match) {
            return client;
        }
    }

    bool broadcast_match = true;
    for (int i = 0; (i < ETH_HWADDR_LEN) && broadcast_match; i++) {
        if (buffer->dest.addr[i] != 0xFF) {
            broadcast_match = false;
        }
    }
    if (broadcast_match) {
        return BROADCAST_ID;
    }

    return -1;
}

void rx_return(void)
{
    bool reprocess = true;
    bool notify_clients[SDDF_NET_MAX_CLIENTS] = {false};
    uint16_t drv_length = net_queue_length_consumer(state.rx_queue_drv.active);
    while (reprocess) {
        uint16_t bufs_dequeued = 0;
        uint16_t bufs_enqueued_cli[SDDF_NET_MAX_CLIENTS] = {0};
        uint16_t bufs_enqueued_drv = 0;
        while (bufs_dequeued < drv_length) {
            net_buff_desc_t *buf = net_queue_next_full(state.rx_queue_drv.active, state.rx_queue_drv.capacity, bufs_dequeued);
            bufs_dequeued++;
            
            buf->io_or_offset = buf->io_or_offset - config.data.io_addr;
            uintptr_t buffer_vaddr = buf->io_or_offset + (uintptr_t)config.data.region.vaddr;

            // Cache invalidate after DMA write, so we don't read stale data.
            // This must be performed after the DMA write to avoid reading
            // data that was speculatively fetched before the DMA write.
            //
            // We would invalidate if it worked in usermode. Alas, it
            // does not -- see [1]. The fastest operation that works is a
            // usermode CleanInvalidate (faster than a Invalidate via syscall).
            //
            // [1]: https://developer.arm.com/documentation/ddi0595/2021-06/AArch64-Instructions/DC-IVAC--Data-or-unified-Cache-line-Invalidate-by-VA-to-PoC
            cache_clean_and_invalidate(buffer_vaddr, buffer_vaddr + buf->len);
            int client = get_mac_addr_match((struct ethernet_header *) buffer_vaddr);
            if (client == BROADCAST_ID) {
                int ref_index = buf->io_or_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] == 0);
                // For broadcast packets, set the refcount to number of clients
                // in the system. Only enqueue buffer back to driver if
                // all clients have consumed the buffer.
                buffer_refs[ref_index] = config.num_clients;

                for (int i = 0; i < config.num_clients; i++) {
                    net_buff_desc_t *slot = net_queue_next_empty(state.rx_queue_clients[i].active, state.rx_queue_clients[i].capacity, bufs_enqueued_cli[i]);
                    bufs_enqueued_cli[i]++;
                    slot->io_or_offset = buf->io_or_offset;
                    slot->len = buf->len;
                }
            } else if (client >= 0) {
                int ref_index = buf->io_or_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] == 0);
                buffer_refs[ref_index] = 1;

                net_buff_desc_t *slot = net_queue_next_empty(state.rx_queue_clients[client].active, state.rx_queue_clients[client].capacity, bufs_enqueued_cli[client]);
                bufs_enqueued_cli[client]++;
                slot->io_or_offset = buf->io_or_offset;
                slot->len = buf->len;
            } else {
                net_buff_desc_t *slot = net_queue_next_empty(state.rx_queue_drv.free, state.rx_queue_drv.capacity, bufs_enqueued_drv);
                bufs_enqueued_drv++;
                slot->io_or_offset = buf->io_or_offset + config.data.io_addr;
            }
        }

        net_queue_publish_dequeued(state.rx_queue_drv.active, bufs_dequeued);
        net_queue_publish_enqueued(state.rx_queue_drv.free, bufs_enqueued_drv);
        notify_drv |= bufs_enqueued_drv;
        for (int client = 0; client < config.num_clients; client++) {
            net_queue_publish_enqueued(state.rx_queue_clients[client].active, bufs_enqueued_cli[client]);
            notify_clients[client] |= bufs_enqueued_cli[client];
        }

        net_request_signal_active(&state.rx_queue_drv);
        reprocess = false;

        drv_length = net_queue_length_consumer(state.rx_queue_drv.active);
        if (drv_length) {
            net_cancel_signal_active(&state.rx_queue_drv);
            reprocess = true;
        }
    }

    for (int client = 0; client < config.num_clients; client++) {
        if (notify_clients[client] && net_require_signal_active(&state.rx_queue_clients[client])) {
            net_cancel_signal_active(&state.rx_queue_clients[client]);
            sddf_notify(config.clients[client].conn.id);
        }
    }
}

void rx_provide(void)
{
    uint16_t bufs_enqueued = 0;
    for (int client = 0; client < config.num_clients; client++) {
        bool reprocess = true;
        uint16_t cli_length = net_queue_length_consumer(state.rx_queue_clients[client].free);
        while (reprocess) {
            uint16_t bufs_dequeued = 0;
            while (bufs_dequeued < cli_length) {
                net_buff_desc_t *buf = net_queue_next_full(state.rx_queue_clients[client].free, state.rx_queue_clients[client].capacity, bufs_dequeued);
                bufs_dequeued++;
                assert(!(buf->io_or_offset % NET_BUFFER_SIZE)
                       && (buf->io_or_offset < NET_BUFFER_SIZE * state.rx_queue_clients[client].capacity));

                int ref_index = buf->io_or_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] != 0);

                buffer_refs[ref_index]--;

                if (buffer_refs[ref_index] != 0) {
                    continue;
                }

                // To avoid having to perform a cache clean here we ensure that
                // the DMA region is only mapped in read only. This avoids the
                // case where pending writes are only written to the buffer
                // memory after DMA has occurred.
                net_buff_desc_t *slot = net_queue_next_empty(state.rx_queue_drv.free, state.rx_queue_drv.capacity, bufs_enqueued);
                bufs_enqueued++;
                slot->io_or_offset = buf->io_or_offset + config.data.io_addr;
            }

            net_queue_publish_dequeued(state.rx_queue_clients[client].free, bufs_dequeued);
            net_request_signal_free(&state.rx_queue_clients[client]);
            reprocess = false;

            cli_length = net_queue_length_consumer(state.rx_queue_clients[client].free);
            if (cli_length) {
                net_cancel_signal_free(&state.rx_queue_clients[client]);
                reprocess = true;
            }
        }
    }
    net_queue_publish_enqueued(state.rx_queue_drv.free, bufs_enqueued);
    notify_drv |= bufs_enqueued;

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
    // Maybe only publish drv free tail index after both functions?
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
