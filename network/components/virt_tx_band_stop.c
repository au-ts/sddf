/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/cache.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <ethernet_config.h>
#include <stdint.h>

#define DRIVER 0
#define TIMER 1
#define CLIENT_CH 2

net_queue_t *tx_free_drv;
net_queue_t *tx_active_drv;
net_queue_t *tx_free_cli0;
net_queue_t *tx_active_cli0;

uintptr_t buffer_data_region_cli0_vaddr;
uintptr_t buffer_data_region_cli0_paddr;
uintptr_t buffer_data_region_cli1_paddr;

#define TIME_WINDOW (10 * NS_IN_MS)
uint64_t current_tick = 0;
typedef struct client_usage {
    uint64_t last_tick;
    uint64_t curr_bits;
    uint64_t max_bits;
} client_usage_t;

typedef struct state {
    net_queue_handle_t tx_queue_drv;
    net_queue_handle_t tx_queue_clients[NUM_NETWORK_CLIENTS];
    client_usage_t client_usage[NUM_NETWORK_CLIENTS];
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

        if (state.client_usage[client].last_tick != current_tick) {
            state.client_usage[client].curr_bits = 0;
            state.client_usage[client].last_tick = current_tick;
        }

        bool reprocess = true;
        while (reprocess) {
            while (!net_queue_empty_active(&state.tx_queue_clients[client])
                    && state.client_usage[client].curr_bits < state.client_usage[client].max_bits) {
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
                state.client_usage[client].curr_bits += (buffer.len * 8);
                enqueued = true;
            }

            net_request_signal_active(&state.tx_queue_clients[client]);
            reprocess = false;

            if (!net_queue_empty_active(&state.tx_queue_clients[client])) {
                net_cancel_signal_active(&state.tx_queue_clients[client]);
                if (state.client_usage[client].curr_bits < state.client_usage[client].max_bits) {
                    reprocess = true;
                } else {
                    sddf_timer_set_timeout(TIMER, TIME_WINDOW);
                }
            }
        }
    }

    if (enqueued && net_require_signal_active(&state.tx_queue_drv)) {
        net_cancel_signal_active(&state.tx_queue_drv);
        microkit_deferred_notify(DRIVER);
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
            microkit_notify(client + CLIENT_CH);
        }
    }
}

void notified(microkit_channel ch)
{
    current_tick = sddf_timer_time_now(TIMER) / TIME_WINDOW;
    tx_return();
    tx_provide();
}

void init(void)
{
    microkit_dbg_puts("In band stop\n");
    /* Set up driver queues */
    net_queue_init(&state.tx_queue_drv, tx_free_drv, tx_active_drv, NET_TX_QUEUE_CAPACITY_DRIV);

    /* Setup client queues and state */
    net_queue_info_t queue_info[NUM_NETWORK_CLIENTS] = {0};
    uintptr_t client_vaddrs[NUM_NETWORK_CLIENTS] = {0};
    net_virt_queue_info(microkit_name, tx_free_cli0, tx_active_cli0, queue_info);
    net_mem_region_vaddr(microkit_name, client_vaddrs, buffer_data_region_cli0_vaddr);

    for (int i = 0; i < NUM_NETWORK_CLIENTS; i++) {
        net_queue_init(&state.tx_queue_clients[i], queue_info[i].free, queue_info[i].active, queue_info[i].capacity);
        state.buffer_region_vaddrs[i] = client_vaddrs[i];
    }

    state.buffer_region_paddrs[0] = buffer_data_region_cli0_paddr;
#if NUM_NETWORK_CLIENTS > 1
    state.buffer_region_paddrs[1] = buffer_data_region_cli1_paddr;
#endif

    state.client_usage[0].max_bits = 2000000;
    state.client_usage[1].max_bits = 2000000;

    tx_provide();
}
