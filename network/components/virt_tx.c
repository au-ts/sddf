/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/util/cache.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#include "net_virt_tx_config.h"

net_virt_tx_config_t config;

typedef struct state {
    net_queue_handle_t tx_queue_drv;
    net_queue_handle_t tx_queue_clients[SDDF_NET_MAX_CLIENTS];
} state_t;

state_t state;

int extract_offset(uintptr_t *phys)
{
    for (int client = 0; client < config.num_clients; client++) {
        if (*phys >= config.clients[client].buffer_data_region_paddr
            && *phys < config.clients[client].buffer_data_region_paddr + state.tx_queue_clients[client].capacity * NET_BUFFER_SIZE) {
            *phys = *phys - config.clients[client].buffer_data_region_paddr;
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

                cache_clean(buffer.io_or_offset + config.clients[client].buffer_data_region_vaddr,
                            buffer.io_or_offset + config.clients[client].buffer_data_region_vaddr + buffer.len);

                buffer.io_or_offset = buffer.io_or_offset + config.clients[client].buffer_data_region_paddr;
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
        microkit_deferred_notify(config.drv_id);
    }
}

void tx_return(void)
{
    bool reprocess = true;
    bool notify_clients[SDDF_NET_MAX_CLIENTS] = {false};
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
            microkit_notify(config.clients[client].id);
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
    sddf_memcpy(&config, net_virt_tx_data, net_virt_tx_data_len);

    /* Set up driver queues */
    net_queue_init(&state.tx_queue_drv, config.free_drv, config.active_drv, config.capacity_drv);

    for (int i = 0; i < config.num_clients; i++) {
        net_queue_init(&state.tx_queue_clients[i], config.clients[i].free, config.clients[i].active, config.clients[i].capacity);
    }

    tx_provide();
}
