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

net_queue_handle_t rx_queue_virt;
net_queue_handle_t rx_queue_cli;

void rx_return(void)
{
    bool enqueued = false;
    bool reprocess = true;

    while (reprocess) {
        while (!net_queue_empty_active(&rx_queue_virt) && !net_queue_empty_free(&rx_queue_cli)) {
            net_buff_desc_t cli_buffer, virt_buffer = {0};
            int err = net_dequeue_free(&rx_queue_cli, &cli_buffer);
            assert(!err);

            if (cli_buffer.io_or_offset % NET_BUFFER_SIZE
                || cli_buffer.io_or_offset >= NET_BUFFER_SIZE * rx_queue_cli.capacity) {
                sddf_dprintf("COPY|LOG: Client provided offset %lx which is not buffer aligned or outside of buffer region\n",
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

            enqueued = true;
        }

        net_request_signal_active(&rx_queue_virt);

        /* Only request signal from client if incoming packets from multiplexer are awaiting free buffers */
        if (!net_queue_empty_active(&rx_queue_virt)) {
            net_request_signal_free(&rx_queue_cli);
        } else {
            net_cancel_signal_free(&rx_queue_cli);
        }

        reprocess = false;

        if (!net_queue_empty_active(&rx_queue_virt) && !net_queue_empty_free(&rx_queue_cli)) {
            net_cancel_signal_active(&rx_queue_virt);
            net_cancel_signal_free(&rx_queue_cli);
            reprocess = true;
        }
    }

    if (enqueued && net_require_signal_active(&rx_queue_cli)) {
        net_cancel_signal_active(&rx_queue_cli);
        sddf_notify(config.client.id);
    }

    if (enqueued && net_require_signal_free(&rx_queue_virt)) {
        net_cancel_signal_free(&rx_queue_virt);
        sddf_deferred_notify(config.virt_rx.id);
    }
}

void notified(sddf_channel ch)
{
    rx_return();
}

void init(void)
{
    assert(net_config_check_magic(&config));
    /* Set up the queues */
    net_queue_init(&rx_queue_cli, config.client.free_queue.vaddr, config.client.active_queue.vaddr,
                   config.client.num_buffers);
    net_queue_init(&rx_queue_virt, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);

    net_buffers_init(&rx_queue_cli, 0);
}
