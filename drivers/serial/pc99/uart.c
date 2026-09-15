/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>
#include <sddf/resources/device.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>
#include <uart.h>

int tx_ready(void)
{
    return read(SERIAL_LSR) & SERIAL_LSR_TRANSMITTER_EMPTY;
}

int rx_ready(void)
{
    return read(SERIAL_LSR) & SERIAL_LSR_DATA_READY;
}

static void tx_provide(void)
{
    bool transferred = false;
    char c;
    while (!serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        serial_dequeue(&tx_queue_handle, &c);
        while (!tx_ready());
        write(SERIAL_THR, c);
        transferred = true;
    }

    if (transferred && serial_require_consumer_signal(&tx_queue_handle)) {
        serial_cancel_consumer_signal(&tx_queue_handle);
        microkit_notify(config.tx.id);
    }
}

static void rx_return(void)
{
    bool enqueued = false;
    while (rx_ready() && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
        char c = (char)read(SERIAL_RBR);
        serial_enqueue(&rx_queue_handle, c);
        enqueued = true;
    }

    if (enqueued) {
        microkit_notify(config.rx.id);
    }
}

static void handle_irq(void)
{
    uint8_t iir = read(SERIAL_IIR) >> 1;
    if (iir & RX_DATA_AVAIL) {
        rx_return();
    }
}

void notified(microkit_channel ch)
{
    if (ch == config.tx.id) {
        tx_provide();
    } else if (ch == config.rx.id) {
        rx_return();
    } else if (ch == IRQ_ID) {
        handle_irq();
        microkit_deferred_irq_ack(IRQ_ID);
    } else {
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
    }
}

void post_init()
{
}
