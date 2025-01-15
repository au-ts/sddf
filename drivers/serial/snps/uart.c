/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include "uart.h"

__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

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
    bool transferred = false;
    char c;
    while ((*REG_PTR(UART_LSR) & UART_LSR_THRE) && !serial_dequeue(&tx_queue_handle, &c)) {
        *REG_PTR(UART_THR) = c;
        transferred = true;
    }

    /* If transmit FIFO is full and we still have data to be sent, enable TX IRQ */
    if ((*REG_PTR(UART_LSR) & UART_LSR_THRE) == 0
        && !serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        *REG_PTR(UART_IER) |= UART_IER_ETBEI;
    } else {
        *REG_PTR(UART_IER) &= ~UART_IER_ETBEI;
    }

    if (transferred && serial_require_consumer_signal(&tx_queue_handle)) {
        serial_cancel_consumer_signal(&tx_queue_handle);
        microkit_notify(config.tx.id);
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
            int err = serial_enqueue(&rx_queue_handle, c);
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

    if (enqueued) {
        microkit_notify(config.rx.id);
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

    assert(serial_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    uart_base = (uintptr_t)device_resources.regions[0].region.vaddr;

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
    set_baud(config.default_baud);

    /* Enable both Recieve Data Available and Transmit Holding Register Empty IRQs. */
    *REG_PTR(UART_IER) = (UART_IER_ERBFI | UART_IER_ETBEI);

    if (config.rx_enabled) {
        serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    }
    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);
}

void notified(microkit_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();
        microkit_deferred_irq_ack(ch);
    } else if (ch == config.tx.id) {
        tx_provide();
    } else if (ch == config.rx.id) {
        rx_return();
    } else {
        LOG_DRIVER("received notification on unexpected channel\n");
    }
}
