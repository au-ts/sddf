/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <uart.h>

#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2

typedef struct config {
    void *uart_regs;
    void *rx_queue;
    void *tx_queue;
    void *rx_data;
    void *tx_data;
    uint64_t rx_capacity;
    uint64_t tx_capacity;
    uint64_t default_baud;
    bool rx_enabled;
} config_t;

config_t config;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

volatile pl011_uart_regs_t *uart_regs;

/*
 * BaudDivInt + BaudDivFrac/64 = (RefFreq/ (16 x BaudRate))
 */
static void set_baud(long bps)
{
    float baud_div = PL011_UART_REF_CLOCK / (16 * bps);
    uint32_t baud_div_int = (uint32_t)baud_div;
    uint32_t baud_div_frac = (uint32_t)((baud_div * 64) + 0.5);

    /* Minimum divide ratio possible is 1 */
    assert(baud_div_int >= 1);

    /* Maximum divide ratio is 0xFFFF */
    assert(baud_div_int < 0xFFFF || (baud_div_int == 0xFFFF && baud_div_frac == 0));

    uart_regs->ibrd = baud_div_int;
    uart_regs->fbrd = baud_div_frac;
}

static void tx_provide(void)
{
    bool reprocess = true;
    bool transferred = false;
    while (reprocess) {
        char c;
        while (!(uart_regs->fr & PL011_FR_TXFF) && !serial_dequeue(&tx_queue_handle, &tx_queue_handle.queue->head, &c)) {
            uart_regs->dr = (uint32_t)c;
            transferred = true;
        }

        serial_request_producer_signal(&tx_queue_handle);
        /* If transmit fifo is full and there is data remaining to be sent, enable interrupt when fifo is no longer full */
        if (uart_regs->fr & PL011_FR_TXFF && !serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
            uart_regs->imsc |= PL011_IMSC_TX_INT;
        } else {
            uart_regs->imsc &= ~PL011_IMSC_TX_INT;
        }
        reprocess = false;

        if (!(uart_regs->fr & PL011_FR_TXFF) && !serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
            serial_cancel_producer_signal(&tx_queue_handle);
            uart_regs->imsc &= ~PL011_IMSC_TX_INT;
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
        while (!(uart_regs->fr & PL011_FR_RXFE) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            char c = (char)(uart_regs->dr & PL011_DR_DATA_MASK);
            serial_enqueue(&rx_queue_handle, &rx_queue_handle.queue->tail, c);
            enqueued = true;
        }

        if (!(uart_regs->fr & PL011_FR_RXFE) && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            /* Disable rx interrupts until virtualisers queue is no longer empty. */
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

    if (enqueued && serial_require_producer_signal(&rx_queue_handle)) {
        serial_cancel_producer_signal(&rx_queue_handle);
        microkit_notify(RX_CH);
    }
}

static void handle_irq(void)
{
    uint32_t uart_int_reg = uart_regs->mis;
    while (uart_int_reg & (PL011_IMSC_RX_TIMEOUT | PL011_IMSC_RX_INT) || uart_int_reg & PL011_IMSC_TX_INT) {
        if (uart_int_reg & (PL011_IMSC_RX_TIMEOUT | PL011_IMSC_RX_INT)) {
            rx_return();
        }
        if (uart_int_reg & PL011_IMSC_TX_INT) {
            tx_provide();
        }
        uart_int_reg = uart_regs->mis;
    }
}

static void uart_setup(void)
{
    uart_regs = config.uart_regs;

    /* Wait for UART to finish transmitting. */
    while (uart_regs->fr & PL011_FR_UART_BUSY);

    /* Disable the UART - UART must be disabled before control registers are reprogrammed. */
    uart_regs->tcr &= ~(PL011_CR_RX_EN | PL011_CR_TX_EN | PL011_CR_UART_EN);

    /* Configure stop bit length to 1 */
    uart_regs->lcr_h &= ~(PL011_LCR_2_STP_BITS);

    /* Set data length to 8 */
    uart_regs->lcr_h |= (0b11 < PL011_LCR_WLEN_SHFT);

    /* Configure the reference clock and baud rate. Difficult to use automatic detection here as it requires the next incoming character to be 'a' or 'A'. */
    set_baud(config.default_baud);

    /* Enable FIFOs */
    uart_regs->lcr_h |= PL011_LCR_FIFO_EN;

    /* Disable parity checking */
    uart_regs->lcr_h |= PL011_LCR_PARTY_EN;

    /* Enable receive interrupts when FIFO level exceeds 1/8 or after 32 ticks */
    if (config.rx_enabled) {
        uart_regs->ifls &= ~(PL011_IFLS_RX_MASK << PL011_IFLS_RX_SHFT);
        uart_regs->imsc |= (PL011_IMSC_RX_TIMEOUT | PL011_IMSC_RX_INT);
    }

    /* Enable transmit interrupts if the FIFO drops below 1/8 - used when the write fifo becomes full */
    uart_regs->ifls &= ~(PL011_IFLS_TX_MASK << PL011_IFLS_TX_SHFT);
    uart_regs->imsc |= PL011_IMSC_TX_INT;

    /* Enable the UART */
    uart_regs->tcr |= PL011_CR_UART_EN;

    /* Enable transmit */
    uart_regs->tcr |= PL011_CR_TX_EN;

    /* Enable receive */
    if (config.rx_enabled) {
        uart_regs->tcr |= PL011_CR_RX_EN;
    }
}

void init(void)
{
    config = (config_t) {
        .uart_regs = (void *)0x5000000,
        .rx_queue = (void *)0x4000000,
        .tx_queue = (void *)0x4001000,
        .rx_data = (void *)0x4002000,
        .tx_data = (void *)0x4004000,
        .rx_capacity = 0x2000,
        .tx_capacity = 0x2000,
        .default_baud = 115200,
        .rx_enabled = true,
    };

    uart_setup();

    if (config.rx_enabled) {
        serial_queue_init(&rx_queue_handle, config.rx_queue, config.rx_capacity, config.rx_data);
    }
    serial_queue_init(&tx_queue_handle, config.tx_queue, config.tx_capacity, config.tx_data);
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case IRQ_CH:
        handle_irq();
        microkit_deferred_irq_ack(ch);
        break;
    case TX_CH:
        tx_provide();
        break;
    case RX_CH:
        uart_regs->imsc |= (PL011_IMSC_RX_TIMEOUT | PL011_IMSC_RX_INT);
        rx_return();
        break;
    default:
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
        break;
    }
}
