/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <sddf/network/constants.h>
#include <sddf/network/queue.h>
#include <sddf/network/util.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/util/cache.h>

#ifdef MICROKIT
#include <microkit.h>
#include <ethernet_config.h>

/* Notification channels */
#define DRIVER_CH 0
#define CLIENT_CH 1

/* Queue regions */
net_queue_t *rx_free_drv;
net_queue_t *rx_active_drv;
net_queue_t *rx_free_cli0;
net_queue_t *rx_active_cli0;

/* Buffer data regions */
uintptr_t buffer_data_vaddr;
uintptr_t buffer_data_paddr;


void notify_delayed(seL4_CPtr cap) {
    microkit_notify_delayed(cap - BASE_OUTPUT_NOTIFICATION_CAP);
}

#else

extern void notify_delayed(seL4_CPtr cap);

#endif

/* Used to signify that a packet has come in for the broadcast address and does not match with
 * any particular client. */
#define BROADCAST_ID (NUM_NETWORK_CLIENTS + 1)

struct client {
    uint64_t rx_free;
    uint64_t rx_active;
    uint8_t client_ch;
    uint8_t client_cap;
}

struct resources {
    const char *name;
    uint64_t rx_free_drv;
    uint64_t rx_active_drv;
    uint64_t buffer_data_vaddr;
    uint64_t buffer_data_paddr;
    uint8_t driver_ch;
    seL4_CPtr drv_cap;
    struct client clients[NUM_NETWORK_CLIENTS];
};

struct resources resources;

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
    while (reprocess) {
        while (!net_queue_empty_active(&state.rx_queue_drv)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&state.rx_queue_drv, &buffer);
            assert(!err);

            buffer.io_or_offset = buffer.io_or_offset - buffer_data_paddr;
            uintptr_t buffer_vaddr = buffer.io_or_offset + buffer_data_vaddr;

            // Cache invalidate after DMA write, so we don't read stale data.
            // This must be performed after the DMA write to avoid reading
            // data that was speculatively fetched before the DMA write.
            //
            // We would invalidate if it worked in usermode. Alas, it
            // does not -- see [1]. The fastest operation that works is a
            // usermode CleanInvalidate (faster than a Invalidate via syscall).
            //
            // [1]: https://developer.arm.com/documentation/ddi0595/2021-06/AArch64-Instructions/DC-IVAC--Data-or-unified-Cache-line-Invalidate-by-VA-to-PoC
            cache_clean_and_invalidate(buffer_vaddr, buffer_vaddr + buffer.len);
            int client = get_mac_addr_match((struct ethernet_header *) buffer_vaddr);
            if (client == BROADCAST_ID) {
                int ref_index = buffer.io_or_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] == 0);
                // For broadcast packets, set the refcount to number of clients
                // in the system. Only enqueue buffer back to driver if
                // all clients have consumed the buffer.
                buffer_refs[ref_index] = NUM_NETWORK_CLIENTS;

                for (int i = 0; i < NUM_NETWORK_CLIENTS; i++) {
                    err = net_enqueue_active(&state.rx_queue_clients[i], buffer);
                    assert(!err);
                    notify_clients[i] = true;
                }
                continue;
            } else if (client >= 0) {
                int ref_index = buffer.io_or_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] == 0);
                buffer_refs[ref_index] = 1;

                err = net_enqueue_active(&state.rx_queue_clients[client], buffer);
                assert(!err);
                notify_clients[client] = true;
            } else {
                buffer.io_or_offset = buffer.io_or_offset + buffer_data_paddr;
                err = net_enqueue_free(&state.rx_queue_drv, buffer);
                assert(!err);
                notify_drv = true;
            }
        }
        net_request_signal_active(&state.rx_queue_drv);
        reprocess = false;

        if (!net_queue_empty_active(&state.rx_queue_drv)) {
            net_cancel_signal_active(&state.rx_queue_drv);
            reprocess = true;
        }
    }

    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        if (notify_clients[client] && net_require_signal_active(&state.rx_queue_clients[client])) {
            net_cancel_signal_active(&state.rx_queue_clients[client]);
            seL4_Signal(client + CLIENT_CH);
        }
    }
}

void rx_provide(void)
{
    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        bool reprocess = true;
        while (reprocess) {
            while (!net_queue_empty_free(&state.rx_queue_clients[client])) {
                net_buff_desc_t buffer;
                int err = net_dequeue_free(&state.rx_queue_clients[client], &buffer);
                assert(!err);
                assert(!(buffer.io_or_offset % NET_BUFFER_SIZE)
                       && (buffer.io_or_offset < NET_BUFFER_SIZE * state.rx_queue_clients[client].capacity));

                int ref_index = buffer.io_or_offset / NET_BUFFER_SIZE;
                assert(buffer_refs[ref_index] != 0);

                buffer_refs[ref_index]--;

                if (buffer_refs[ref_index] != 0) {
                    continue;
                }

                // To avoid having to perform a cache clean here we ensure that
                // the DMA region is only mapped in read only. This avoids the
                // case where pending writes are only written to the buffer
                // memory after DMA has occured.
                buffer.io_or_offset = buffer.io_or_offset + buffer_data_paddr;
                err = net_enqueue_free(&state.rx_queue_drv, buffer);
                assert(!err);
                notify_drv = true;
            }

            net_request_signal_free(&state.rx_queue_clients[client]);
            reprocess = false;

            if (!net_queue_empty_free(&state.rx_queue_clients[client])) {
                net_cancel_signal_free(&state.rx_queue_clients[client]);
                reprocess = true;
            }
        }
    }

    if (notify_drv && net_require_signal_free(&state.rx_queue_drv)) {
        net_cancel_signal_free(&state.rx_queue_drv);
        notify_delayed(resources.drv_cap);
        notify_drv = false;
    }
}

void notified(unsigned int ch)
{
    rx_return();
    rx_provide();
}

void init(void)
{
#ifdef MICROKIT
    resources = (struct resources) {
        .name = microkit_name,
        .rx_free_drv = rx_free_drv,
        .rx_active_drv = rx_active_drv,
        .buffer_data_vaddr = buffer_data_vaddr,
        .buffer_data_paddr = buffer_data_paddr,
        .driver_ch = DRIVER_CH,
        .drv_cap = BASE_OUTPUT_NOTIFICATION_CAP + DRIVER_CH,
        .clients = {0},
    }

    resources.clients[0] = (struct client) {
        .rx_free = rx_free_cli0,
        .rx_used = rx_active_cli0,
        .client_ch = CLIENT_CH,
        .client_cap = BASE_OUTPUT_NOTIFICATION_CAP + CLIENT_CH,

#endif

    uint64_t macs[NUM_NETWORK_CLIENTS] = {0};
    net_queue_info_t queue_info[NUM_NETWORK_CLIENTS] = {0};

    net_virt_mac_addrs(resources.name, macs);
    net_virt_queue_info(resources.name, resources.clients[0].rx_free, resources.clients[0].rx_active, queue_info);

    /* Set up client queues */
    for (int i = 0; i < NUM_NETWORK_CLIENTS; i++) {
        net_set_mac_addr((uint8_t *) &state.mac_addrs[i], macs[i]);
        net_queue_init(&state.rx_queue_clients[i], queue_info[i].free, queue_info[i].active, queue_info[i].capacity);
    }

     /* Set up driver queues */
    net_queue_init(&state.rx_queue_drv, resources.rx_free_drv, resources.rx_active_drv, NET_RX_QUEUE_CAPACITY_DRIV);
    net_buffers_init(&state.rx_queue_drv, resources.buffer_data_paddr);

    if (net_require_signal_free(&state.rx_queue_drv)) {
        net_cancel_signal_free(&state.rx_queue_drv);
        notify_delayed(DRIVER_CH);
    }
}
