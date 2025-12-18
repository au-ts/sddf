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

#ifdef PANCAKE_NETWORK_VIRT
// Memory layout for Pancake (must match .pnk file)
#define CONFIG_DRIVER_ID          0
#define DRV_QUEUE_BASE           10
#define CLI_QUEUE_BASE           30
#define CLI_DATA_IO_BASE         100
#define CLI_CONN_ID_BASE         150
#define NUM_CLIENTS              200
#define NOTIFY_CLIENTS_BASE      210

static char cml_memory[1024*20];
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
    unsigned long cml_heap_sz = 1024*10;
    unsigned long cml_stack_sz = 1024*10;
    cml_heap = cml_memory;
    cml_stack = cml_heap + cml_heap_sz;
    cml_stackend = cml_stack + cml_stack_sz;
}
#endif

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

#ifdef PANCAKE_NETWORK_VIRT
extern void notified(sddf_channel ch);
#else
void notified(sddf_channel ch)
{
    tx_return();
    tx_provide();
}
#endif

void init(void)
{
    assert(net_config_check_magic(&config));

#ifdef PANCAKE_NETWORK_VIRT
    init_pancake_mem();
    
    uintptr_t *pnk_mem = (uintptr_t *) cml_heap;
    
    // Store driver ID
    pnk_mem[CONFIG_DRIVER_ID] = config.driver.id;
    
    // Store driver queue info
    pnk_mem[DRV_QUEUE_BASE] = (uintptr_t)config.driver.free_queue.vaddr;
    pnk_mem[DRV_QUEUE_BASE + 1] = (uintptr_t)config.driver.active_queue.vaddr;
    pnk_mem[DRV_QUEUE_BASE + 2] = config.driver.num_buffers;
    
    // Store client queue info and data IO addresses
    for (int i = 0; i < config.num_clients; i++) {
        pnk_mem[CLI_QUEUE_BASE + i * 4] = (uintptr_t)config.clients[i].conn.free_queue.vaddr;
        pnk_mem[CLI_QUEUE_BASE + i * 4 + 1] = (uintptr_t)config.clients[i].conn.active_queue.vaddr;
        pnk_mem[CLI_QUEUE_BASE + i * 4 + 2] = config.clients[i].conn.num_buffers;
        pnk_mem[CLI_QUEUE_BASE + i * 4 + 3] = (uintptr_t)config.clients[i].data.region.vaddr;
        
        pnk_mem[CLI_DATA_IO_BASE + i] = config.clients[i].data.io_addr;
        pnk_mem[CLI_CONN_ID_BASE + i] = config.clients[i].conn.id;
    }
    
    pnk_mem[NUM_CLIENTS] = config.num_clients;
    
    // Initialize notify flags
    for (int i = 0; i < SDDF_NET_MAX_CLIENTS; i++) {
        pnk_mem[NOTIFY_CLIENTS_BASE + i] = 0;
    }
    
    net_queue_init(&state.tx_queue_drv, config.driver.free_queue.vaddr, config.driver.active_queue.vaddr,
                   config.driver.num_buffers);
    
    for (int i = 0; i < config.num_clients; i++) {
        net_queue_init(&state.tx_queue_clients[i], config.clients[i].conn.free_queue.vaddr,
                       config.clients[i].conn.active_queue.vaddr, config.clients[i].conn.num_buffers);
    }
    
    cml_main();
#else

    /* Set up driver queues */
    net_queue_init(&state.tx_queue_drv, config.driver.free_queue.vaddr, config.driver.active_queue.vaddr,
                   config.driver.num_buffers);

    for (int i = 0; i < config.num_clients; i++) {
        net_queue_init(&state.tx_queue_clients[i], config.clients[i].conn.free_queue.vaddr,
                       config.clients[i].conn.active_queue.vaddr, config.clients[i].conn.num_buffers);
    }

    tx_provide();
#endif
}
