/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#define VIRT_RX_CH 0
#define CLIENT_CH 1

net_queue_handle_t rx_queue_virt;
net_queue_handle_t rx_queue_cli;

net_queue_t *rx_free_virt;
net_queue_t *rx_active_virt;
net_queue_t *rx_free_cli;
net_queue_t *rx_active_cli;

uintptr_t virt_buffer_data_region;
uintptr_t cli_buffer_data_region;

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
            uintptr_t cli_addr = cli_buffer_data_region + cli_buf->io_or_offset;
            uintptr_t virt_addr = virt_buffer_data_region + virt_buf->io_or_offset;
            sddf_memcpy((void *)cli_addr, (void *)virt_addr, virt_buf->len);

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
        microkit_notify(CLIENT_CH);
    }

    if (notify_neighbours && net_require_signal_free(&rx_queue_virt)) {
        net_cancel_signal_free(&rx_queue_virt);
        microkit_deferred_notify(VIRT_RX_CH);
    }
}

void notified(microkit_channel ch)
{
    rx_return();
}

void init(void)
{
    size_t cli_queue_capacity, virt_queue_capacity = 0;
    net_copy_queue_capacity(microkit_name, &cli_queue_capacity, &virt_queue_capacity);

    /* Set up the queues */
    net_queue_init(&rx_queue_cli, rx_free_cli, rx_active_cli, cli_queue_capacity);
    net_queue_init(&rx_queue_virt, rx_free_virt, rx_active_virt, virt_queue_capacity);

    net_buffers_init(&rx_queue_cli, 0);
}
