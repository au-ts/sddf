/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/cache.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#ifdef MICROKIT
#include <microkit.h>
#include <ethernet_config.h>

/* Microkit specific stuff */
#define DRIVER 0
#define CLIENT_CH 1

net_queue_t *tx_free_drv;
net_queue_t *tx_active_drv;
net_queue_t *tx_free_cli0;
net_queue_t *tx_active_cli0;

uintptr_t buffer_data_region_cli0_vaddr;
uintptr_t buffer_data_region_cli0_paddr;

#endif /* MICROKIT */

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
    bool enqueued = false;
    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
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

                cache_clean(buffer.io_or_offset + state.buffer_region_vaddrs[client],
                            buffer.io_or_offset + state.buffer_region_vaddrs[client] + buffer.len);

                buffer.io_or_offset = buffer.io_or_offset + state.buffer_region_paddrs[client];
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
        notify_delayed(resources.drv_cap);
    }
}

void tx_return(void)
{
    bool reprocess = true;
    bool notify_clients[NUM_NETWORK_CLIENTS] = {false};
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

    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        if (notify_clients[client] && net_require_signal_free(&state.tx_queue_clients[client])) {
            net_cancel_signal_free(&state.tx_queue_clients[client]);
            seL4_Signal(resources[client].client_cap);
        }
    }
}

void notified(unsigned int ch)
{
    tx_return();
    tx_provide();
}

void init(void)
{
#ifdef MICROKIT
    resources = (struct resources) {
        .name = microkit_name,
        .tx_free_drv = tx_free_drv,
        .tx_active_drv = tx_active_drv,
        .drv_ch = DRIVER_CH,
        .drv_cap = BASE_OUTPUT_NOTIFICATION_CAP + DRIVER_CH,
        .clients = {0},
    }

    resources.clients[0] = (struct client) {
        .tx_free = tx_free_cli0,
        .tx_used = tx_active_cli0,
        .buffer_data_region_vaddr = buffer_data_region_cli0_vaddr,
        .buffer_data_region_paddr = buffer_data_region_cli0_paddr,
        .client_ch = CLIENT_CH,
        .client_cap = BASE_OUTPUT_NOTIFICATION_CAP + CLIENT_CH,
    }
#endif

    /* Set up driver queues */
    net_queue_init(&state.tx_queue_drv, resources.tx_free_drv, resources.tx_active_drv, NET_TX_QUEUE_CAPACITY_DRIV);

    /* Setup client queues and state */
    net_queue_info_t queue_info[NUM_NETWORK_CLIENTS] = {0};
    uintptr_t client_vaddrs[NUM_NETWORK_CLIENTS] = {0};
    net_virt_queue_info(resources.name, resources.clients[0].tx_free, resources.clients[0].tx_active, queue_info);
    net_mem_region_vaddr(resources.name, client_vaddrs, resources.clients[0].buffer_data_region_paddr);

    for (int i = 0; i < NUM_NETWORK_CLIENTS; i++) {
        net_queue_init(&state.tx_queue_clients[i], queue_info[i].free, queue_info[i].active, queue_info[i].capacity);
        state.buffer_region_vaddrs[i] = client_vaddrs[i];
    }

    state.buffer_region_paddrs[0] = buffer_data_region_cli0_paddr;
#if NUM_NETWORK_CLIENTS > 1
    state.buffer_region_paddrs[1] = buffer_data_region_cli1_paddr;
#endif

    tx_provide();
}
