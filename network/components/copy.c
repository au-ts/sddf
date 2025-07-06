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
    bool notify_neighbours = false;
    bool reprocess = true;
    uint16_t virt_length = net_queue_length_consumer(rx_queue_virt.active);
    uint16_t cli_length = net_queue_length_consumer(rx_queue_cli.free);
    while (reprocess) {
        uint16_t bufs_dequeued = 0;
        while (bufs_dequeued < virt_length && bufs_dequeued < cli_length) {
            net_buff_desc_t *cli_buf = net_queue_next_full(rx_queue_cli.free, rx_queue_cli.capacity, bufs_dequeued);
            if (cli_buf->io_or_offset % NET_BUFFER_SIZE
                || cli_buf->io_or_offset >= NET_BUFFER_SIZE * rx_queue_cli.capacity) {
                sddf_dprintf("COPY|LOG: Client provided offset %lx which is not buffer aligned or outside of buffer region\n",
                             cli_buf->io_or_offset);
                // These need to be handled correctly...
                continue;
            }

            net_buff_desc_t *virt_buf = net_queue_next_full(rx_queue_virt.active, rx_queue_virt.capacity, bufs_dequeued);
            void *cli_addr = config.client_data.vaddr + cli_buf->io_or_offset;
            void *virt_addr = config.device_data.vaddr + virt_buf->io_or_offset;
            sddf_memcpy(cli_addr, virt_addr, virt_buf->len);

            net_buff_desc_t *cli_slot = net_queue_next_empty(rx_queue_cli.active, rx_queue_cli.capacity, bufs_dequeued);
            cli_slot->io_or_offset = cli_buf->io_or_offset;
            cli_slot->len = virt_buf->len;

            net_buff_desc_t *virt_slot = net_queue_next_empty(rx_queue_virt.free, rx_queue_virt.capacity, bufs_dequeued);
            virt_slot->io_or_offset = virt_buf->io_or_offset;

            bufs_dequeued ++;
        }

        net_queue_publish_dequeued(rx_queue_cli.free, bufs_dequeued);
        net_queue_publish_dequeued(rx_queue_virt.active, bufs_dequeued);
        net_queue_publish_enqueued(rx_queue_cli.active, bufs_dequeued);
        net_queue_publish_enqueued(rx_queue_virt.free, bufs_dequeued);
        notify_neighbours |= bufs_dequeued;

        net_request_signal_active(&rx_queue_virt);
        /* Only request signal from client if incoming packets from multiplexer are awaiting free buffers */
        if (virt_length - bufs_dequeued) {
            net_request_signal_free(&rx_queue_cli);
        } else {
            net_cancel_signal_free(&rx_queue_cli);
        }
        reprocess = false;

        virt_length = net_queue_length_consumer(rx_queue_virt.active);
        cli_length = net_queue_length_consumer(rx_queue_cli.free);
        if (virt_length && cli_length) {
            net_cancel_signal_active(&rx_queue_virt);
            net_cancel_signal_free(&rx_queue_cli);
            reprocess = true;
        }
    }

    if (notify_neighbours && net_require_signal_active(&rx_queue_cli)) {
        net_cancel_signal_active(&rx_queue_cli);
        sddf_notify(config.client.id);
    }

    if (notify_neighbours && net_require_signal_free(&rx_queue_virt)) {
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
