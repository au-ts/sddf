/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <serial_config.h>
#include "uart.h"

#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2

serial_queue_t *rx_queue;
serial_queue_t *tx_queue;

char *rx_data;
char *tx_data;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

/* UART device registers */
volatile uintptr_t uart_base;

#define REG_PTR(off)     ((volatile uint32_t *)((uart_base) + (off)))

static void set_baud(unsigned long baud)
{
    /*  Divisor Latch Access Bit (DLAB) of the LCR must be set.
    *   These registers share their address with the FIFO's.
    */

    uint32_t lcr_val = *REG_PTR(UART_LCR);

    *REG_PTR(UART_LCR) |= UART_LCR_DLAB;

    /* baud rate = (serial_clock_freq) / (16 * divisor) */
    uint16_t divisor = DIV_ROUND_CLOSEST(UART_CLK, 16 * baud);

    *REG_PTR(UART_DLH) |= (divisor >> 8) & DL_MASK;
    *REG_PTR(UART_DLL) |= divisor & DL_MASK;

    /* Restore the LCR */
    *REG_PTR(UART_LCR) = lcr_val;
}

static void tx_provide(void)
{
    bool reprocess = true;
    bool transferred = false;
    while (reprocess) {
        char c;

        while ((*REG_PTR(UART_LSR) & UART_LSR_THRE)
               && !serial_dequeue(&tx_queue_handle, &tx_queue_handle.queue->head, &c)) {
            *REG_PTR(UART_THR) = c;
            transferred = true;
        }

        serial_request_producer_signal(&tx_queue_handle);
        /* If transmit FIFO is full and we still have data to be sent, enable TX IRQ */
        if ((*REG_PTR(UART_LSR) & UART_LSR_THRE) == 0
            && !serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
            *REG_PTR(UART_IER) |= UART_IER_ETBEI;
        } else {
            *REG_PTR(UART_IER) &= ~UART_IER_ETBEI;
        }
        reprocess = false;

        if ((*REG_PTR(UART_LSR) & UART_LSR_THRE)
            && !serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
            serial_cancel_producer_signal(&tx_queue_handle);
            *REG_PTR(UART_IER) &= ~UART_IER_ETBEI;
            reprocess = true;
        }
    }

    if (transferred && serial_require_consumer_signal(&tx_queue_handle)) {
        serial_cancel_consumer_signal(&tx_queue_handle);
        microkit_notify(TX_CH);
    }
}

static void rx_return(void)
{
    bool reprocess = true;
    bool enqueued = false;
    while (reprocess) {
        while ((*REG_PTR(UART_LSR) & UART_LSR_DR)
               && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            char c = *REG_PTR(UART_RBR);
            int err = serial_enqueue(&rx_queue_handle, &rx_queue_handle.queue->tail, c);
            assert(!err);
            enqueued = true;
        }

        /* If we have more RX device data available, but no space in the queue with the virtualiser,
         * we disable RX IRQs until space becomes available. */
        if ((*REG_PTR(UART_LSR) & UART_LSR_DR) && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            *REG_PTR(UART_IER) &= ~UART_IER_ERBFI;
            serial_request_consumer_signal(&rx_queue_handle);
        }
        reprocess = false;

        /* While RX data is still available, we enable the RX IRQ and continue processing */
        if ((*REG_PTR(UART_LSR) & UART_LSR_DR) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            serial_cancel_consumer_signal(&rx_queue_handle);
            *REG_PTR(UART_LSR) |= UART_IER_ERBFI;
            reprocess = true;
        }
    }

    if (enqueued && serial_require_producer_signal(&rx_queue_handle)) {
        serial_cancel_producer_signal(&rx_queue_handle);
        microkit_notify(RX_CH);
    }
}

static void handle_irq(void)
{
    uint32_t irq_status = *REG_PTR(UART_IIR);
    uint32_t line_status = *REG_PTR(UART_LSR);
    if (irq_status & UART_IIR_RX) {
        rx_return();
    }

    if (irq_status & UART_IIR_THR_EMPTY) {
        tx_provide();
    }

    if (line_status & UART_ABNORMAL) {
        sddf_dprintf("UART|ERROR: Uart device encountered an error with status register %u\n", line_status);
        /* Clear the UART errors */
        line_status |= UART_ABNORMAL;
    }
}

void init(void)
{
    LOG_DRIVER("initialising\n");

    /* Ensure that the FIFO's are empty */
    while (!(*REG_PTR(UART_LSR) & UART_LSR_THRE));

    /* Reset the UART device - this disables RX and TX */
    *REG_PTR(UART_SSR) |= UART_SSR_UR;

    /* Setup the Modem Control Register */
    *REG_PTR(UART_MCR) |= (UART_MCR_DTR | UART_MCR_RTS);

    /* Clear and enable the FIFO's*/
    *REG_PTR(UART_FCR) = UART_FCR_CE;

    /* Set defaults for the UART Line control register */
    *REG_PTR(UART_LCR) |= UART_LCR_DEFAULT;

    /* Reset IIR */
    *REG_PTR(UART_IIR) = 0x1;

    /* Set the baud rate */
    set_baud(UART_DEFAULT_BAUD);

    /* Enable both Recieve Data Available and Transmit Holding Register Empty IRQs. */
    *REG_PTR(UART_IER) = (UART_IER_ERBFI | UART_IER_ETBEI);

#if !SERIAL_TX_ONLY
    serial_queue_init(&rx_queue_handle, rx_queue, SERIAL_RX_DATA_REGION_CAPACITY_DRIV, rx_data);
#endif
    serial_queue_init(&tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_CAPACITY_DRIV, tx_data);
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case IRQ_CH:
        handle_irq();
        microkit_deferred_irq_ack(IRQ_CH);
        return;
    case TX_CH:
        tx_provide();
        break;
    case RX_CH:
        rx_return();
        break;
    default:
        LOG_DRIVER("received notification on unexpected channel\n");
        break;
    }
}
