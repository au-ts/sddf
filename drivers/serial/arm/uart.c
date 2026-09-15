/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/resources/device.h>
#include <sddf/serial/config.h>
#include <sddf/util/printf.h>
#include <uart.h>

static void tx_provide(void)
{
    bool transferred = false;
    char c;
    while (!(uart_regs->fr & PL011_FR_TXFF) && !serial_dequeue(&tx_queue_handle, &c)) {
        uart_regs->dr = (uint32_t)c;
        transferred = true;
    }

    /* If there is data remaining to be sent, enable interrupt when fifo is no longer full */
    if (!serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        uart_regs->imsc |= PL011_IMSC_TX_INT;
    } else {
        uart_regs->imsc &= ~PL011_IMSC_TX_INT;
    }

    if (transferred && serial_require_consumer_signal(&tx_queue_handle)) {
        serial_cancel_consumer_signal(&tx_queue_handle);
        sddf_notify(config.tx.id);
    }
}

static void rx_return(void)
{
    bool reprocess = true;
    bool enqueued = false;
    while (reprocess) {
        while (!(uart_regs->fr & PL011_FR_RXFE) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            char c = (char)(uart_regs->dr & PL011_DR_DATA_MASK);
            serial_enqueue(&rx_queue_handle, c);
            enqueued = true;
        }

        if (!(uart_regs->fr & PL011_FR_RXFE) && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            /* Disable rx interrupts until virtualisers queue is no longer full. */
            uart_regs->imsc &= ~(PL011_IMSC_RX_TIMEOUT | PL011_IMSC_RX_INT);
            serial_request_consumer_signal(&rx_queue_handle);
        }
        reprocess = false;

        if (!(uart_regs->fr & PL011_FR_RXFE) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            serial_cancel_consumer_signal(&rx_queue_handle);
            uart_regs->imsc |= (PL011_IMSC_RX_TIMEOUT | PL011_IMSC_RX_INT);
            reprocess = true;
        }
    }

    if (enqueued) {
        sddf_notify(config.rx.id);
    }
}

static void handle_irq(void)
{
    uint32_t uart_int_reg = uart_regs->mis;
    while (uart_int_reg & (PL011_IMSC_RX_TIMEOUT | PL011_IMSC_RX_INT) || uart_int_reg & PL011_IMSC_TX_INT) {
        if (config.rx_enabled && uart_int_reg & (PL011_IMSC_RX_TIMEOUT | PL011_IMSC_RX_INT)) {
            rx_return();
        }
        if (uart_int_reg & PL011_IMSC_TX_INT) {
            tx_provide();
        }
        uart_int_reg = uart_regs->mis;
    }
}

void notified(sddf_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();
        sddf_deferred_irq_ack(ch);
    } else if (ch == config.tx.id) {
        tx_provide();
    } else if (ch == config.rx.id) {
        uart_regs->imsc |= (PL011_IMSC_RX_TIMEOUT | PL011_IMSC_RX_INT);
        rx_return();
    } else {
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
    }
}

void post_init()
{
}
