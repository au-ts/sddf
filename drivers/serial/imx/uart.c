/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include <sddf/serial/config.h>
#include <stdbool.h>
#include <stdint.h>
#include <uart.h>

static void tx_provide(void)
{
    bool transferred = false;
    char c;
    while (!(uart_regs->ts & UART_TST_TX_FIFO_FULL) && !serial_dequeue(&tx_queue_handle, &c)) {
        uart_regs->txd = (uint32_t)c;
        transferred = true;
    }

    /* If there is data remaining to be sent, enable interrupt when fifo is no longer full */
    if (!serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        uart_regs->cr1 |= UART_CR1_TX_READY_INT;
    } else {
        uart_regs->cr1 &= ~UART_CR1_TX_READY_INT;
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
        while (!(uart_regs->ts & UART_TST_RX_FIFO_EMPTY) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            char c = (char) uart_regs->rxd;
            serial_enqueue(&rx_queue_handle, c);
            enqueued = true;
        }

        if (!(uart_regs->ts & UART_TST_RX_FIFO_EMPTY) && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            /* Disable rx interrupts until virtualisers queue is no longer full. */
            uart_regs->cr1 &= ~UART_CR1_RX_READY_INT;
            serial_request_consumer_signal(&rx_queue_handle);
        }
        reprocess = false;

        if (!(uart_regs->ts & UART_TST_RX_FIFO_EMPTY) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            serial_cancel_consumer_signal(&rx_queue_handle);
            uart_regs->cr1 |= UART_CR1_RX_READY_INT;
            reprocess = true;
        }
    }

    if (enqueued) {
        sddf_notify(config.rx.id);
    }
}

static void handle_irq(void)
{
    uint32_t uart_sr1 = uart_regs->sr1;
    uint32_t uart_cr1 = uart_regs->cr1;
    while (uart_sr1 & UART_SR1_ABNORMAL || uart_sr1 & UART_SR1_RX_RDY
           || (uart_cr1 & UART_CR1_TX_READY_INT && uart_sr1 & UART_SR1_TX_RDY)) {
        if (config.rx_enabled && uart_sr1 & UART_SR1_RX_RDY) {
            rx_return();
        }
        if (uart_cr1 & UART_CR1_TX_READY_INT && uart_sr1 & UART_SR1_TX_RDY) {
            tx_provide();
        }
        if (uart_sr1 & UART_SR1_ABNORMAL) {
            sddf_dprintf("UART|ERROR: Uart device encountered an error with status register %u\n", uart_sr1);
            uart_regs->sr1 |= UART_SR1_ABNORMAL;
        }
        uart_sr1 = uart_regs->sr1;
        uart_cr1 = uart_regs->cr1;
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
        uart_regs->cr1 |= UART_CR1_RX_READY_INT;
        rx_return();
    } else {
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
    }
}

void post_init()
{
}
