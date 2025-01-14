/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".serial_client_config"))) serial_client_config_t config;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

uint32_t local_head;

void init(void)
{
    serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);

    serial_putchar_init(config.tx.id, &tx_queue_handle);
    sddf_printf("Hello world! I am %s.\nPlease give me character!\n", microkit_name);
}

uint16_t char_count;
void notified(microkit_channel ch)
{
    bool reprocess = true;
    char c;
    while (reprocess) {
        while (!serial_dequeue(&rx_queue_handle, &rx_queue_handle.queue->head, &c)) {
            if (c == '\r') {
                sddf_putchar_unbuffered('\\');
                sddf_putchar_unbuffered('r');
            } else {
                sddf_putchar_unbuffered(c);
            }
            char_count++;
            if (char_count % 10 == 0) {
                sddf_printf("\n%s has received %u characters so far!\n", microkit_name, char_count);
            }
        }

        serial_request_producer_signal(&rx_queue_handle);
        reprocess = false;

        if (!serial_queue_empty(&rx_queue_handle, rx_queue_handle.queue->head)) {
            serial_cancel_producer_signal(&rx_queue_handle);
            reprocess = true;
        }
    }
}
