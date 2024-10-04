/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/cache.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#define DRIVER 0
#define CLIENT_CH 1

net_queue_t *tx_free_drv;
net_queue_t *tx_active_drv;
net_queue_t *tx_free_cli0;
net_queue_t *tx_active_cli0;

uintptr_t buffer_data_region_cli0_vaddr;
uintptr_t buffer_data_region_cli0_paddr;
uintptr_t buffer_data_region_cli1_paddr;

typedef struct state {
    net_queue_handle_t tx_queue_drv;
    net_queue_handle_t tx_queue_clients[NUM_NETWORK_CLIENTS];
    uintptr_t buffer_region_vaddrs[NUM_NETWORK_CLIENTS];
    uintptr_t buffer_region_paddrs[NUM_NETWORK_CLIENTS];
} state_t;

state_t state;

int extract_offset(uintptr_t *phys)
{
    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        if (*phys >= state.buffer_region_paddrs[client]
            && *phys < state.buffer_region_paddrs[client] + state.tx_queue_clients[client].capacity * NET_BUFFER_SIZE) {
            *phys = *phys - state.buffer_region_paddrs[client];
            return client;
        }
    }
    return -1;
}

void tx_provide(void)
{
    uint16_t bufs_enqueued = 0;
    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        bool reprocess = true;
        uint16_t cli_length = net_queue_length_consumer(state.tx_queue_clients[client].active);
        while (reprocess) {
            uint16_t bufs_dequeued = 0;
            while (bufs_dequeued < cli_length) {
                net_buff_desc_t *buf = net_queue_next_full(state.tx_queue_clients[client].active, state.tx_queue_clients[client].capacity, bufs_dequeued);
                bufs_dequeued++;
                if (buf->io_or_offset % NET_BUFFER_SIZE
                    || buf->io_or_offset >= NET_BUFFER_SIZE * state.tx_queue_clients[client].capacity) {
                    sddf_dprintf("VIRT_TX|LOG: Client provided offset %lx which is not buffer aligned or outside of buffer region\n",
                                 buf->io_or_offset);
                    // TODO handle this
                    // err = net_enqueue_free(&state.tx_queue_clients[client], buffer);
                    // assert(!err);
                    // continue;
                }

                cache_clean(buf->io_or_offset + state.buffer_region_vaddrs[client],
                            buf->io_or_offset + state.buffer_region_vaddrs[client] + buf->len);
                
                net_buff_desc_t *slot = net_queue_next_empty(state.tx_queue_drv.active, state.tx_queue_drv.capacity, bufs_enqueued);
                bufs_enqueued++;
                slot->io_or_offset = buf->io_or_offset + state.buffer_region_paddrs[client];
                slot->len = buf->len;
            }

            net_queue_publish_dequeued(state.tx_queue_clients[client].active, bufs_dequeued);
            net_request_signal_active(&state.tx_queue_clients[client]);
            reprocess = false;

            cli_length = net_queue_length_consumer(state.tx_queue_clients[client].active);
            if (cli_length) {
                net_cancel_signal_active(&state.tx_queue_clients[client]);
                reprocess = true;
            }
        }
    }

    net_queue_publish_enqueued(state.tx_queue_drv.active, bufs_enqueued);

    if (bufs_enqueued && net_require_signal_active(&state.tx_queue_drv)) {
        net_cancel_signal_active(&state.tx_queue_drv);
        microkit_deferred_notify(DRIVER);
    }
}

void tx_return(void)
{
    bool reprocess = true;
    bool notify_clients[NUM_NETWORK_CLIENTS] = {false};
    uint16_t drv_length = net_queue_length_consumer(state.tx_queue_drv.free);
    while (reprocess) {
        uint16_t bufs_dequeued = 0;
        uint16_t bufs_enqueued_cli[NUM_NETWORK_CLIENTS] = {0};
        while (bufs_dequeued < drv_length) {
            net_buff_desc_t *buf = net_queue_next_full(state.tx_queue_drv.free, state.tx_queue_drv.capacity, bufs_dequeued);
            bufs_dequeued++;

            uint64_t phys = buf->io_or_offset;
            int client = extract_offset(&phys);
            assert(client >= 0);

            net_buff_desc_t *slot = net_queue_next_empty(state.tx_queue_clients[client].free, state.tx_queue_clients[client].capacity, bufs_enqueued_cli[client]);
            bufs_enqueued_cli[client]++;
            slot->io_or_offset = phys;
        }

        net_queue_publish_dequeued(state.tx_queue_drv.free, bufs_dequeued);
        for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
            net_queue_publish_enqueued(state.tx_queue_clients[client].free, bufs_enqueued_cli[client]);
            notify_clients[client] |= bufs_enqueued_cli[client];
        }

        net_request_signal_free(&state.tx_queue_drv);
        reprocess = false;

        drv_length = net_queue_length_consumer(state.tx_queue_drv.free);
        if (drv_length) {
            net_cancel_signal_free(&state.tx_queue_drv);
            reprocess = true;
        }
    }

    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        if (notify_clients[client] && net_require_signal_free(&state.tx_queue_clients[client])) {
            net_cancel_signal_free(&state.tx_queue_clients[client]);
            microkit_notify(client + CLIENT_CH);
        }
    }
}

void notified(microkit_channel ch)
{
    tx_return();
    tx_provide();
}

void init(void)
{
    /* Set up driver queues */
    net_queue_init(&state.tx_queue_drv, tx_free_drv, tx_active_drv, NET_TX_QUEUE_CAPACITY_DRIV);

    /* Setup client queues and state */
    net_queue_info_t queue_info[NUM_NETWORK_CLIENTS] = {0};
    uintptr_t client_vaddrs[NUM_NETWORK_CLIENTS] = {0};
    net_virt_queue_info(microkit_name, tx_free_cli0, tx_active_cli0, queue_info);
    net_mem_region_vaddr(microkit_name, client_vaddrs, buffer_data_region_cli0_vaddr);

    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        net_queue_init(&state.tx_queue_clients[client], queue_info[client].free, queue_info[client].active, queue_info[client].capacity);
        state.buffer_region_vaddrs[client] = client_vaddrs[client];
    }

    state.buffer_region_paddrs[0] = buffer_data_region_cli0_paddr;
#if NUM_NETWORK_CLIENTS > 1
    state.buffer_region_paddrs[1] = buffer_data_region_cli1_paddr;
#endif

    tx_provide();
}
