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

#ifdef PANCAKE_NETWORK_VIRT
// Memory layout for Pancake (must match .pnk file)
#define CONFIG_DRIVER_ID          0
#define DRV_QUEUE_BASE           10
#define CLI_QUEUE_BASE           30
#define CLI_MAC_ADDR_BASE        100
#define DATA_IO_ADDR             200
#define DATA_REGION_VADDR        201
#define NUM_CLIENTS              202
#define BUFFER_REFS_BASE         210
#define CLI_CONN_ID_BASE         1210
#define NOTIFY_DRV_FLAG          1250
#define NOTIFY_CLIENTS_BASE      1260

static char cml_memory[1024*30];
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

extern void cml_main(void);

void cml_exit(int arg) {
    microkit_dbg_puts("ERROR! We should not be getting here\n");
}

void cml_err(int arg) {
    if (arg == 3) {
        microkit_dbg_puts("Memory not ready for entry. You may have not run the init code yet, or be trying to enter during an FFI call.\n");
    }
    cml_exit(arg);
}

void cml_clear() {
    microkit_dbg_puts("Trying to clear cache\n");
}

void init_pancake_mem() {
    unsigned long cml_heap_sz = 1024*15;
    unsigned long cml_stack_sz = 1024*15;
    cml_heap = cml_memory;
    cml_stack = cml_heap + cml_heap_sz;
    cml_stackend = cml_stack + cml_stack_sz;
}
#endif

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

#ifndef PANCAKE_NETWORK_VIRT
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
    bool notify_clients[SDDF_NET_MAX_CLIENTS] = { false };
    while (reprocess) {
        while (!net_queue_empty_active(&state.rx_queue_drv)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&state.rx_queue_drv, &buffer);
            assert(!err);

            buffer.io_or_offset = buffer.io_or_offset - config.data.io_addr;
            uintptr_t buffer_vaddr = buffer.io_or_offset + (uintptr_t)config.data.region.vaddr;

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
                buffer_refs[ref_index] = config.num_clients;

                for (int i = 0; i < config.num_clients; i++) {
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
                buffer.io_or_offset = buffer.io_or_offset + config.data.io_addr;
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

    for (int client = 0; client < config.num_clients; client++) {
        if (notify_clients[client] && net_require_signal_active(&state.rx_queue_clients[client])) {
            net_cancel_signal_active(&state.rx_queue_clients[client]);
            sddf_notify(config.clients[client].conn.id);
        }
    }
}

void rx_provide(void)
{
    for (int client = 0; client < config.num_clients; client++) {
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
                buffer.io_or_offset = buffer.io_or_offset + config.data.io_addr;
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
        sddf_deferred_notify(config.driver.id);
        notify_drv = false;
    }
}
#endif

#ifdef PANCAKE_NETWORK_VIRT
extern void notified(sddf_channel ch);
#else
void notified(sddf_channel ch)
{
    rx_return();
    rx_provide();
}
#endif

void init(void)
{
    assert(net_config_check_magic(&config));

#ifdef PANCAKE_NETWORK_VIRT
    init_pancake_mem();

    uintptr_t *pnk_mem = (uintptr_t *) cml_heap;

    pnk_mem[CONFIG_DRIVER_ID] = config.driver.id;

    pnk_mem[DRV_QUEUE_BASE] = (uintptr_t)config.driver.free_queue.vaddr;
    pnk_mem[DRV_QUEUE_BASE + 1] = (uintptr_t)config.driver.active_queue.vaddr;
    pnk_mem[DRV_QUEUE_BASE + 2] = config.driver.num_buffers;

    pnk_mem[DATA_IO_ADDR] = config.data.io_addr;
    pnk_mem[DATA_REGION_VADDR] = (uintptr_t)config.data.region.vaddr;

    pnk_mem[NUM_CLIENTS] = config.num_clients;

    for (int i = 0; i < config.num_clients; i++) {
        pnk_mem[CLI_QUEUE_BASE + i * 4] = (uintptr_t)config.clients[i].conn.free_queue.vaddr;
        pnk_mem[CLI_QUEUE_BASE + i * 4 + 1] = (uintptr_t)config.clients[i].conn.active_queue.vaddr;
        pnk_mem[CLI_QUEUE_BASE + i * 4 + 2] = config.clients[i].conn.num_buffers;
        pnk_mem[CLI_QUEUE_BASE + i * 4 + 3] = 0; // unused

        pnk_mem[CLI_CONN_ID_BASE + i] = config.clients[i].conn.id;

        for (int j = 0; j < ETH_HWADDR_LEN; j++) {
            pnk_mem[CLI_MAC_ADDR_BASE + i * ETH_HWADDR_LEN + j] = config.clients[i].mac_addr[j];
        }

        /* Print MAC address for hardcoding in Pancake */
        sddf_dprintf("VIRT_RX: Client %d MAC: %02x:%02x:%02x:%02x:%02x:%02x\n",
                     i,
                     config.clients[i].mac_addr[0],
                     config.clients[i].mac_addr[1],
                     config.clients[i].mac_addr[2],
                     config.clients[i].mac_addr[3],
                     config.clients[i].mac_addr[4],
                     config.clients[i].mac_addr[5]);
    }

    for (int i = 0; i < config.driver.num_buffers; i++) {
        pnk_mem[BUFFER_REFS_BASE + i] = 0;
    }

    pnk_mem[NOTIFY_DRV_FLAG] = 0;
    for (int i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        pnk_mem[NOTIFY_CLIENTS_BASE + i] = 0;
    }

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

    cml_main();
#else

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
#endif
}
