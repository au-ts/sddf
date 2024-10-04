/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/constants.h>
#include <sddf/network/queue.h>
#include <sddf/network/util.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/util/cache.h>
#include <ethernet_config.h>

/* Notification channels */
#define DRIVER_CH 0
#define CLIENT_CH 1

/* Used to signify that a packet has come in for the broadcast address and does not match with
 * any particular client. */
#define BROADCAST_ID (NUM_NETWORK_CLIENTS + 1)

/* Queue regions */
net_queue_t *rx_free_drv;
net_queue_t *rx_active_drv;
net_queue_t *rx_free_cli0;
net_queue_t *rx_active_cli0;

/* Buffer data regions */
uintptr_t buffer_data_vaddr;
uintptr_t buffer_data_paddr;

/* In order to handle broadcast packets where the same buffer is given to multiple clients
  * we keep track of a reference count of each buffer and only hand it back to the driver once
  * all clients have returned the buffer. */
uint32_t buffer_refs[NET_RX_QUEUE_CAPACITY_DRIV] = { 0 };

typedef struct state {
    net_queue_handle_t rx_queue_drv;
    net_queue_handle_t rx_queue_clients[NUM_NETWORK_CLIENTS];
    uint8_t mac_addrs[NUM_NETWORK_CLIENTS][ETH_HWADDR_LEN];
} state_t;

state_t state;

/* Boolean to indicate whether a packet has been enqueued into the driver's free queue during notification handling */
static bool notify_drv;

/* Return the client ID if the Mac address is a match to a client, return the broadcast ID if MAC address
  is a broadcast address. */
int get_mac_addr_match(struct ethernet_header *buffer)
{
    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        bool match = true;
        for (int i = 0; (i < ETH_HWADDR_LEN) && match; i++) {
            if (buffer->dest.addr[i] != state.mac_addrs[client][i]) {
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
    bool notify_clients[NUM_NETWORK_CLIENTS] = {false};
    uint16_t drv_length = net_queue_length_consumer(state.rx_queue_drv.active);
    while (reprocess) {
        uint16_t bufs_dequeued = 0;
        uint16_t bufs_enqueued_cli[NUM_NETWORK_CLIENTS] = {0};
        uint16_t bufs_enqueued_drv = 0;
        while (bufs_dequeued < drv_length) {
            net_buff_desc_t *buf = net_queue_next_full(state.rx_queue_drv.active, state.rx_queue_drv.capacity, bufs_dequeued);
            bufs_dequeued++;
            
            uint64_t buffer_offset = buf->io_or_offset - buffer_data_paddr;
            uint64_t virt_vaddr = buffer_data_vaddr + buffer_offset;

            // Cache invalidate after DMA write, so we don't read stale data.
            // This must be performed after the DMA write to avoid reading
            // data that was speculatively fetched before the DMA write.
            //
            // We would invalidate if it worked in usermode. Alas, it
            // does not -- see [1]. The fastest operation that works is a
            // usermode CleanInvalidate (faster than a Invalidate via syscall).
            //
            // [1]: https://developer.arm.com/documentation/ddi0595/2021-06/AArch64-Instructions/DC-IVAC--Data-or-unified-Cache-line-Invalidate-by-VA-to-PoC
            cache_clean_and_invalidate(virt_vaddr, virt_vaddr + buf->len);
            int client = get_mac_addr_match((struct ethernet_header *) virt_vaddr);
            if (client == BROADCAST_ID) {
                int ref_index = buffer_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] == 0);
                // For broadcast packets, set the refcount to number of clients
                // in the system. Only enqueue buffer back to driver if
                // all clients have consumed the buffer.
                buffer_refs[ref_index] = NUM_NETWORK_CLIENTS;

                for (int i = 0; i < NUM_NETWORK_CLIENTS; i++) {
                    net_buff_desc_t *slot = net_queue_next_empty(state.rx_queue_clients[i].active, state.rx_queue_clients[i].capacity, bufs_enqueued_cli[i]);
                    bufs_enqueued_cli[i]++;
                    slot->io_or_offset = buffer_offset;
                    slot->len = buf->len;
                }
            } else if (client >= 0) {
                int ref_index = buffer_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] == 0);
                buffer_refs[ref_index] = 1;

                net_buff_desc_t *slot = net_queue_next_empty(state.rx_queue_clients[client].active, state.rx_queue_clients[client].capacity, bufs_enqueued_cli[client]);
                bufs_enqueued_cli[client]++;
                slot->io_or_offset = buffer_offset;
                slot->len = buf->len;
            } else {
                net_buff_desc_t *slot = net_queue_next_empty(state.rx_queue_drv.free, state.rx_queue_drv.capacity, bufs_enqueued_drv);
                bufs_enqueued_drv++;
                slot->io_or_offset = buf->io_or_offset;
            }
        }

        net_queue_publish_dequeued(state.rx_queue_drv.active, bufs_dequeued);
        net_queue_publish_enqueued(state.rx_queue_drv.free, bufs_enqueued_drv);
        notify_drv |= bufs_enqueued_drv;
        for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
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

    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        if (notify_clients[client] && net_require_signal_active(&state.rx_queue_clients[client])) {
            net_cancel_signal_active(&state.rx_queue_clients[client]);
            microkit_notify(client + CLIENT_CH);
        }
    }
}

void rx_provide(void)
{
    uint16_t bufs_enqueued = 0;
    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
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
                slot->io_or_offset = buf->io_or_offset + buffer_data_paddr;
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
        microkit_deferred_notify(DRIVER_CH);
        notify_drv = false;
    }
}

void notified(microkit_channel ch)
{
    rx_return();
    rx_provide();
    // Maybe only publish drv free tail index after both functions?
}

void init(void)
{
    uint64_t macs[NUM_NETWORK_CLIENTS] = {0};
    net_queue_info_t queue_info[NUM_NETWORK_CLIENTS] = {0};

    net_virt_mac_addrs(microkit_name, macs);
    net_virt_queue_info(microkit_name, rx_free_cli0, rx_active_cli0, queue_info);

    /* Set up client queues */
    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        net_set_mac_addr((uint8_t *) &state.mac_addrs[client], macs[client]);
        net_queue_init(&state.rx_queue_clients[client], queue_info[client].free, queue_info[client].active, queue_info[client].capacity);
    }

    /* Set up driver queues */
    net_queue_init(&state.rx_queue_drv, rx_free_drv, rx_active_drv, NET_RX_QUEUE_CAPACITY_DRIV);
    net_buffers_init(&state.rx_queue_drv, buffer_data_paddr);

    if (net_require_signal_free(&state.rx_queue_drv)) {
        net_cancel_signal_free(&state.rx_queue_drv);
        microkit_deferred_notify(DRIVER_CH);
    }
}
