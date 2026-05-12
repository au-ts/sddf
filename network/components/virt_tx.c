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
    bool enqueued = false;
    for (int client = 0; client < config.num_clients; client++) {
        bool reprocess = true;
        while (reprocess) {
            while (!net_queue_empty_active(&state.tx_queue_clients[client])) {
                net_buff_desc_t buffer;
                int err = net_dequeue_active(&state.tx_queue_clients[client], &buffer);
                assert(!err);

                if (buffer.io_or_offset % NET_BUFFER_SIZE
                    || buffer.io_or_offset >= NET_BUFFER_SIZE * state.tx_queue_clients[client].capacity) {
                    sddf_dprintf("VIRT_TX|LOG: Client provided offset %lx which is not buffer aligned or outside of buffer region\n",
                                 buffer.io_or_offset);
                    err = net_enqueue_free(&state.tx_queue_clients[client], buffer);
                    assert(!err);
                    continue;
                }

                uintptr_t buffer_vaddr = buffer.io_or_offset + (uintptr_t)config.clients[client].data.region.vaddr;
                cache_clean(buffer_vaddr, buffer_vaddr + buffer.len);

                buffer.io_or_offset = buffer.io_or_offset + config.clients[client].data.io_addr;
                err = net_enqueue_active(&state.tx_queue_drv, buffer);
                assert(!err);
                enqueued = true;
            }

            net_request_signal_active(&state.tx_queue_clients[client]);
            reprocess = false;

            if (!net_queue_empty_active(&state.tx_queue_clients[client])) {
                net_cancel_signal_active(&state.tx_queue_clients[client]);
                reprocess = true;
            }
        }
    }

    if (enqueued && net_require_signal_active(&state.tx_queue_drv)) {
        net_cancel_signal_active(&state.tx_queue_drv);
        sddf_deferred_notify(config.driver.id);
    }
}

void tx_return(void)
{
    bool reprocess = true;
    bool notify_clients[SDDF_NET_MAX_CLIENTS] = { false };
    while (reprocess) {
        while (!net_queue_empty_free(&state.tx_queue_drv)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&state.tx_queue_drv, &buffer);
            assert(!err);

            int client = extract_offset(&buffer.io_or_offset);
            assert(client >= 0);

            err = net_enqueue_free(&state.tx_queue_clients[client], buffer);
            assert(!err);
            notify_clients[client] = true;
        }

        net_request_signal_free(&state.tx_queue_drv);
        reprocess = false;

        if (!net_queue_empty_free(&state.tx_queue_drv)) {
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
