/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include <sddf/serial/config.h>
#include <uart.h>

static void tx_provide(void)
{
    bool transferred = false;
    char c;
    while (!(uart_regs->sr & AML_UART_TX_FULL) && !serial_dequeue(&tx_queue_handle, &c)) {
        uart_regs->wfifo = (uint32_t)c;
        transferred = true;
    }

    /* If there is data remaining to be sent, enable interrupt when fifo is no longer full */
    if (!serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        uart_regs->cr |= AML_UART_TX_INT_EN;
    } else {
        uart_regs->cr &= ~AML_UART_TX_INT_EN;
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
        while (!(uart_regs->sr & AML_UART_RX_EMPTY) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            char c = (char) uart_regs->rfifo;
            serial_enqueue(&rx_queue_handle, c);
            enqueued = true;
        }

        if (!(uart_regs->sr & AML_UART_RX_EMPTY) && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            /* Disable rx interrupts until virtualisers queue is no longer full. */
            uart_regs->cr &= ~AML_UART_RX_INT_EN;
            serial_request_consumer_signal(&rx_queue_handle);
        }
        reprocess = false;

        if (!(uart_regs->sr & AML_UART_RX_EMPTY) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            serial_cancel_consumer_signal(&rx_queue_handle);
            uart_regs->cr |= AML_UART_RX_INT_EN;
            reprocess = true;
        }
    }

    if (enqueued) {
        sddf_notify(config.rx.id);
    }
}

static void handle_irq(void)
{
    uint32_t uart_sr = uart_regs->sr;
    uint32_t uart_cr = uart_regs->cr;
    while (uart_sr & UART_INTR_ABNORMAL || !(uart_sr & AML_UART_RX_EMPTY)
           || (uart_cr & AML_UART_TX_INT_EN && !(uart_sr & AML_UART_TX_FULL))) {
        if (config.rx_enabled && !(uart_sr & AML_UART_RX_EMPTY)) {
            rx_return();
        }
        if (uart_cr & AML_UART_TX_INT_EN && !(uart_sr & AML_UART_TX_FULL)) {
            tx_provide();
        }
        if (uart_sr & UART_INTR_ABNORMAL) {
            sddf_dprintf("UART|ERROR: Uart device encountered an error with status register %u\n", uart_sr);
            uart_regs->cr |= AML_UART_CLEAR_ERR;
        }
        uart_sr = uart_regs->sr;
        uart_cr = uart_regs->cr;
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
        uart_regs->cr |= AML_UART_RX_INT_EN;
        rx_return();
    } else {
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
    }
}

void post_init()
{
}
