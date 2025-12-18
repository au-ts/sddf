/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <os/sddf.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".net_copy_config"))) net_copy_config_t config;

#ifdef PANCAKE_NETWORK_COPY
// Memory layout for Pancake (must match .pnk file)
#define CONFIG_CLIENT_ID         0
#define CONFIG_VIRT_RX_ID        1
#define CLI_QUEUE_BASE           10
#define VIRT_QUEUE_BASE          30
#define CLIENT_DATA_VADDR        200
#define DEVICE_DATA_VADDR        201
#define CLI_NUM_BUFFERS          202
#define VIRT_NUM_BUFFERS         203

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

net_queue_handle_t rx_queue_virt;
net_queue_handle_t rx_queue_cli;

void rx_return(void)
{
    bool client_enqueued = false;
    bool virt_enqueued = false;
    bool reprocess = true;

    while (reprocess) {
        while (!net_queue_empty_active(&rx_queue_virt)) {
            /* Copy into client buffer if available, else return to rx virt free queue */
            if (!net_queue_empty_free(&rx_queue_cli)) {
                net_buff_desc_t cli_buffer, virt_buffer = { 0 };
                int err = net_dequeue_free(&rx_queue_cli, &cli_buffer);
                assert(!err);

                if (cli_buffer.io_or_offset % NET_BUFFER_SIZE
                    || cli_buffer.io_or_offset >= NET_BUFFER_SIZE * rx_queue_cli.capacity) {
                    sddf_dprintf("COPY|LOG: Client provided offset %lx which is not buffer aligned or outside of "
                                 "buffer region\n",
                                 cli_buffer.io_or_offset);
                    continue;
                }

                err = net_dequeue_active(&rx_queue_virt, &virt_buffer);
                assert(!err);

                void *cli_addr = config.client_data.vaddr + cli_buffer.io_or_offset;
                void *virt_addr = config.device_data.vaddr + virt_buffer.io_or_offset;

                sddf_memcpy(cli_addr, virt_addr, virt_buffer.len);
                cli_buffer.len = virt_buffer.len;
                virt_buffer.len = 0;

                err = net_enqueue_active(&rx_queue_cli, cli_buffer);
                assert(!err);

                err = net_enqueue_free(&rx_queue_virt, virt_buffer);
                assert(!err);

                client_enqueued = true;
            } else {
                net_buff_desc_t virt_buffer = { 0 };
                int err = net_dequeue_active(&rx_queue_virt, &virt_buffer);
                assert(!err);

                err = net_enqueue_free(&rx_queue_virt, virt_buffer);
                assert(!err);
            }
            virt_enqueued = true;
        }

        net_request_signal_active(&rx_queue_virt);
        reprocess = false;

        if (!net_queue_empty_active(&rx_queue_virt)) {
            net_cancel_signal_active(&rx_queue_virt);
            reprocess = true;
        }
    }

    if (client_enqueued && net_require_signal_active(&rx_queue_cli)) {
        net_cancel_signal_active(&rx_queue_cli);
        sddf_notify(config.client.id);
    }

    if (virt_enqueued && net_require_signal_free(&rx_queue_virt)) {
        net_cancel_signal_free(&rx_queue_virt);
        sddf_deferred_notify(config.virt_rx.id);
    }
}

#ifdef PANCAKE_NETWORK_COPY
extern void notified(sddf_channel ch);
#else
void notified(sddf_channel ch)
{
    rx_return();
}
#endif

void init(void)
{
    assert(net_config_check_magic(&config));
    
#ifdef PANCAKE_NETWORK_COPY
    init_pancake_mem();
    
    uintptr_t *pnk_mem = (uintptr_t *) cml_heap;
    pnk_mem[CONFIG_CLIENT_ID] = config.client.id;
    pnk_mem[CONFIG_VIRT_RX_ID] = config.virt_rx.id;
    
    pnk_mem[CLI_QUEUE_BASE + 0] = (uintptr_t)config.client.free_queue.vaddr;
    pnk_mem[CLI_QUEUE_BASE + 1] = (uintptr_t)config.client.active_queue.vaddr;
    pnk_mem[CLI_QUEUE_BASE + 2] = config.client.num_buffers;
    
    pnk_mem[VIRT_QUEUE_BASE + 0] = (uintptr_t)config.virt_rx.free_queue.vaddr;
    pnk_mem[VIRT_QUEUE_BASE + 1] = (uintptr_t)config.virt_rx.active_queue.vaddr;
    pnk_mem[VIRT_QUEUE_BASE + 2] = config.virt_rx.num_buffers;
    
    pnk_mem[CLIENT_DATA_VADDR] = (uintptr_t)config.client_data.vaddr;
    pnk_mem[DEVICE_DATA_VADDR] = (uintptr_t)config.device_data.vaddr;
    
    pnk_mem[CLI_NUM_BUFFERS] = config.client.num_buffers;
    pnk_mem[VIRT_NUM_BUFFERS] = config.virt_rx.num_buffers;
    
    cml_main();
#endif

    /* Set up the queues */
    net_queue_init(&rx_queue_cli, config.client.free_queue.vaddr, config.client.active_queue.vaddr,
                   config.client.num_buffers);
    net_queue_init(&rx_queue_virt, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);

    net_buffers_init(&rx_queue_cli, 0);
}
