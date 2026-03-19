/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <os/sddf.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <string.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".net_copy_config"))) net_copy_config_t config;

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
                sddf_printf_("COPY active queue after dequeue len %d\n", net_queue_length(rx_queue_virt.active));
                assert(!err);

                sddf_printf_("COPYCFG sizeof=%lu\n", sizeof(net_copy_config_t));
                sddf_printf_("COPYCFG off virt_rx=%lu\n", offsetof(net_copy_config_t, virt_rx));
                sddf_printf_("COPYCFG off client=%lu\n", offsetof(net_copy_config_t, client));
                sddf_printf_("COPYCFG off client_data=%lu\n", offsetof(net_copy_config_t, client_data));
                sddf_printf_("COPYCFG off out_data=%lu\n", offsetof(net_copy_config_t, out_data));
                sddf_printf_("COPYCFG out_data[0].vaddr=%p size=%lu\n",
                             config.out_data[0].vaddr, config.out_data[0].size);
                sddf_printf_("COPYCFG out_data[1].vaddr=%p size=%lu\n",
                             config.out_data[1].vaddr, config.out_data[1].size);

                sddf_printf_("COPY oid=%d out_data.vaddr=%p size=%lu\n",
                     virt_buffer.oid,
                     config.out_data[virt_buffer.oid].vaddr,
                     config.out_data[virt_buffer.oid].size);

                sddf_printf_("COPY (vswitch/free) buffer oid: %d\n", virt_buffer.oid);
                sddf_printf_("COPY addr: %p\n", config.out_data[virt_buffer.oid].vaddr);

                void *cli_addr = config.client_data.vaddr + cli_buffer.io_or_offset;
                void *virt_addr = config.out_data[virt_buffer.oid].vaddr + virt_buffer.io_or_offset;

                sddf_printf("COPY first 14 bytes before copy: "
                "%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x\n",
                    ((uint8_t *)(uintptr_t)virt_addr)[0],
                    ((uint8_t *)(uintptr_t)virt_addr)[1],
                    ((uint8_t *)(uintptr_t)virt_addr)[2],
                    ((uint8_t *)(uintptr_t)virt_addr)[3],
                    ((uint8_t *)(uintptr_t)virt_addr)[4],
                    ((uint8_t *)(uintptr_t)virt_addr)[5],
                    ((uint8_t *)(uintptr_t)virt_addr)[6],
                    ((uint8_t *)(uintptr_t)virt_addr)[7],
                    ((uint8_t *)(uintptr_t)virt_addr)[8],
                    ((uint8_t *)(uintptr_t)virt_addr)[9],
                    ((uint8_t *)(uintptr_t)virt_addr)[10],
                    ((uint8_t *)(uintptr_t)virt_addr)[11],
                    ((uint8_t *)(uintptr_t)virt_addr)[12],
                    ((uint8_t *)(uintptr_t)virt_addr)[13]);

                memcpy(cli_addr, virt_addr, virt_buffer.len);
                cli_buffer.len = virt_buffer.len;
                cli_buffer.oid = virt_buffer.oid;
                virt_buffer.len = 0;

                err = net_enqueue_active(&rx_queue_cli, cli_buffer);
                assert(!err);

                sddf_printf_("COPY virt_buffer.len :%d\n", cli_buffer.len);
                sddf_printf("COPY first 14 bytes after copy: "
                "%02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x %02x\n",
                    ((uint8_t *)(uintptr_t)cli_addr)[0],
                    ((uint8_t *)(uintptr_t)cli_addr)[1],
                    ((uint8_t *)(uintptr_t)cli_addr)[2],
                    ((uint8_t *)(uintptr_t)cli_addr)[3],
                    ((uint8_t *)(uintptr_t)cli_addr)[4],
                    ((uint8_t *)(uintptr_t)cli_addr)[5],
                    ((uint8_t *)(uintptr_t)cli_addr)[6],
                    ((uint8_t *)(uintptr_t)cli_addr)[7],
                    ((uint8_t *)(uintptr_t)cli_addr)[8],
                    ((uint8_t *)(uintptr_t)cli_addr)[9],
                    ((uint8_t *)(uintptr_t)cli_addr)[10],
                    ((uint8_t *)(uintptr_t)cli_addr)[11],
                    ((uint8_t *)(uintptr_t)cli_addr)[12],
                    ((uint8_t *)(uintptr_t)cli_addr)[13]);
                // Dump of the packet sent
                sddf_printf_("COPY returning buffer with offset: %ld\n", virt_buffer.io_or_offset);
                err = net_enqueue_free(&rx_queue_virt, virt_buffer);
                sddf_printf_("COPY free queue after enqueue len %d\n", net_queue_length(rx_queue_virt.free));
                assert(!err);

                client_enqueued = true;
            } else {
                net_buff_desc_t virt_buffer = { 0 };
                int err = net_dequeue_active(&rx_queue_virt, &virt_buffer);
                assert(!err);

                err = net_enqueue_free(&rx_queue_virt, virt_buffer);
                assert(!err);

                sddf_printf_("COPY chosen the weird branch\n");
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
        sddf_printf_("COPY notifying CLIENT\n");
        net_cancel_signal_active(&rx_queue_cli);
        sddf_notify(config.client.id);
    }

    sddf_printf_("COPY RX VSWITCH freeQ len: %d, activeQ len: %d\n", net_queue_length(rx_queue_virt.free), net_queue_length(rx_queue_virt.active));

    if (virt_enqueued && net_require_signal_free(&rx_queue_virt)) {
        sddf_printf_("COPY notifying VSWITCH\n");
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
