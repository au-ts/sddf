/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/util/cache.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".net_virt_tx_config"))) net_virt_tx_config_t config;

typedef struct state {
    net_queue_handle_t tx_queue_drv;
    net_queue_handle_t tx_queue_clients[SDDF_NET_MAX_CLIENTS];
} state_t;

state_t state;

int extract_offset(uintptr_t *phys)
{
    for (int client = 0; client < config.num_clients; client++) {
        if (*phys >= config.clients[client].data.io_addr
            && *phys
                   < config.clients[client].data.io_addr + state.tx_queue_clients[client].capacity * NET_BUFFER_SIZE) {
            *phys = *phys - config.clients[client].data.io_addr;
            return client;
        }
    }
    return -1;
}

void tx_provide(void)
{
    uint16_t bufs_enqueued = 0;
    for (int client = 0; client < config.num_clients; client++) {
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


                uintptr_t buffer_vaddr = buf->io_or_offset + (uintptr_t)config.clients[client].data.region.vaddr;
                cache_clean(buffer_vaddr, buffer_vaddr + buf->len);
                
                net_buff_desc_t *slot = net_queue_next_empty(state.tx_queue_drv.active, state.tx_queue_drv.capacity, bufs_enqueued);
                bufs_enqueued++;
                slot->io_or_offset = buf->io_or_offset + config.clients[client].data.io_addr;
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
        sddf_deferred_notify(config.driver.id);
    }
}

void tx_return(void)
{
    bool reprocess = true;
    bool notify_clients[SDDF_NET_MAX_CLIENTS] = {false};
    uint16_t drv_length = net_queue_length_consumer(state.tx_queue_drv.free);
    while (reprocess) {
        uint16_t bufs_dequeued = 0;
        uint16_t bufs_enqueued_cli[SDDF_NET_MAX_CLIENTS] = {0};
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
        for (int client = 0; client < config.num_clients; client++) {
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

    for (int client = 0; client < config.num_clients; client++) {
        if (notify_clients[client] && net_require_signal_free(&state.tx_queue_clients[client])) {
            net_cancel_signal_free(&state.tx_queue_clients[client]);
            sddf_notify(config.clients[client].conn.id);
        }
    }
}

void notified(sddf_channel ch)
{
    tx_return();
    tx_provide();
}

void init(void)
{
    assert(net_config_check_magic(&config));

    /* Set up driver queues */
    net_queue_init(&state.tx_queue_drv, config.driver.free_queue.vaddr, config.driver.active_queue.vaddr,
                   config.driver.num_buffers);

    for (int i = 0; i < config.num_clients; i++) {
        net_queue_init(&state.tx_queue_clients[i], config.clients[i].conn.free_queue.vaddr,
                       config.clients[i].conn.active_queue.vaddr, config.clients[i].conn.num_buffers);
    }

    tx_provide();
}
