/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <sddf/serial/config.h>
#include <uart.h>

__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;
__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

volatile zynqmp_uart_regs_t *uart_regs;

/*
* BaudDivInt + BaudDivFrac/64 = (RefFreq / (16 x BaudRate))
*/
static void set_baud(long bps)
{
    // Disable UART while configuring baud rate
    // uart_regs->tcr &= ~(1 << 0);  // Clear UARTEN bit

    // float baud_div = ZYNQMP_UART_REF_CLOCK / (16 * bps);
    // uint32_t baud_div_int = (uint32_t)baud_div;
    // uint32_t baud_div_frac = (uint32_t)((baud_div * 64) + 0.5);

    // /* Minimum divide ratio possible is 1 */
    // assert(baud_div_int >= 1);

    // /* Maximum divide ratio is 0xFFFF */
    // assert(baud_div_int < 0xFFFF || (baud_div_int == 0xFFFF && baud_div_frac == 0));

    // uart_regs->ibrd = baud_div_int;
    // uart_regs->fbrd = baud_div_frac;
}

static void tx_provide(void)
{
    // sddf_dprintf("UART|LOG: Inside tx_provide.\n");

    bool transferred = false;
    char c;
    while (!(uart_regs->sr & UART_CHANNEL_STS_TXFULL) && !serial_dequeue(&tx_queue_handle, &c)) {
        // sddf_dprintf("UART|LOG: Inside tx_provide and TX not full, sending %c\n", c);
        uart_regs->fifo = (uint32_t)c;
        transferred = true;
    }

    /* If transmit fifo is full and there is data remaining to be sent, enable interrupt when fifo is no longer full */
    if (uart_regs->sr & UART_CHANNEL_STS_TXFULL && !serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        // sddf_dprintf("UART|LOG: Inside tx_provide and TX FIFO is full.\n");
        uart_regs->cr &= ~UART_CR_TX_EN;
        uart_regs->cr |= UART_CR_TX_DIS;
    } else {
        // sddf_dprintf("UART|LOG: Inside tx_provide and TX FIFO is NOT full but we are inside ELSE of IF.\n");
        uart_regs->cr |= UART_CR_TX_EN;
        uart_regs->cr &= ~UART_CR_TX_DIS;
    }

    if (transferred && serial_require_consumer_signal(&tx_queue_handle)) {
        // sddf_dprintf("UART|LOG: Inside tx_provide and REQ CONS SIG.\n");
        serial_cancel_consumer_signal(&tx_queue_handle);
        microkit_notify(config.tx.id);
    }

    // sddf_dprintf("UART|LOG: Finished tx_provide.\n");
}

static void rx_return(void)
{
    // sddf_dprintf("UART|LOG: Inside rx_return.\n");

    // FIXME: My RX handler does NOT take TIMEOUT into account, should it?

    bool reprocess = true;
    bool enqueued = false;
    while (reprocess) {
        while (!(uart_regs->sr & UART_CHANNEL_STS_RXEMPTY)
               && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            char c = (char)(uart_regs->fifo);
            sddf_dprintf("UART|LOG: Got c: %c\n", c);
            serial_enqueue(&rx_queue_handle, c);
            enqueued = true;
        }

        if (!(uart_regs->sr & UART_CHANNEL_STS_RXEMPTY) && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            /* Disable rx interrupts until virtualisers queue is no longer full. */
            uart_regs->cr &= ~UART_CR_RX_EN;
            uart_regs->cr |= UART_CR_RX_DIS;
            serial_request_consumer_signal(&rx_queue_handle);
        }
        reprocess = false;

        if (!(uart_regs->sr & UART_CHANNEL_STS_RXEMPTY) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            serial_cancel_consumer_signal(&rx_queue_handle);
            uart_regs->cr |= UART_CR_RX_EN;
            uart_regs->cr &= ~UART_CR_RX_DIS;
            reprocess = true;
        }
    }

    if (enqueued) {
        microkit_notify(config.rx.id);
    }
}

int uart_get_char()
{
    if (uart_regs->sr & 0x02U) {
        return 0;
    }

    return uart_regs->fifo;
}

void uart_put_char(int ch)
{
    while (!(uart_regs->sr & UART_CHANNEL_STS_TXEMPTY));
    uart_regs->fifo = ch;
    if (ch == '\r') {
        uart_put_char('\n');
    }
}

static void handle_irq(void)
{
    // FIXME: Do I need to clear the interrupt status or not?
    // uart_regs->isr = XUARTPS_IXR_RXOVR;
    // XUARTPS_IXR_RXEMPTY |
    // XUARTPS_IXR_RXFULL;

    uint32_t uart_cr_reg = uart_regs->cr;
    while (uart_cr_reg & UART_CR_RX_EN || uart_cr_reg & UART_CR_TX_EN) {
        if (uart_cr_reg & UART_CR_RX_EN) {
            rx_return();
        }
        if (uart_cr_reg & UART_CR_TX_EN) {
            tx_provide();
        }
        uart_cr_reg = uart_regs->cr;
    }
}

void uart_put_str(char *str)
{
    while (*str) {
        uart_put_char(*str);
        str++;
    }
}

static void uart_setup(void)
{
    uint32_t ctrl = uart_regs->cr;
    uint32_t mode;

    ctrl |= UART_CR_TX_EN;
    ctrl |= UART_CR_RX_EN;
    ctrl &= ~UART_CR_TX_DIS;
    ctrl &= ~UART_CR_RX_DIS;

    uart_regs->cr = ctrl;

    // The following was adapted from Xilinx xuartps.c

    mode = uart_regs->mr;
    mode &= (~((XUARTPS_MR_CHARLEN_MASK |
                XUARTPS_MR_STOPMODE_MASK |
                XUARTPS_MR_PARITY_MASK)));

    mode |= (XUARTPS_MR_CHARLEN_8_BIT |
             XUARTPS_MR_STOPMODE_1_BIT |
             XUARTPS_MR_PARITY_NONE);

    uart_regs->mr = mode;

    /* Set the RX FIFO trigger at 1 data byte */
    uart_regs->rxwm = 0x01U;

    /* Set the RX timeout to 1 */
    uart_regs->rxtout = 0x01U;

    // Enable interrupt when a new character is added to RX FIFO
    uart_regs->ier =    XUARTPS_IXR_RXOVR;
    // XUARTPS_IXR_RXEMPTY |
    // XUARTPS_IXR_RXFULL;

    uart_put_str("UART|LOG: Initialised UART!\n");

    // FIXME: Below is the code from ARM example driver,
    // maybe incorporate setting baud properly later.

    /* Wait for UART to finish transmitting. */
    // while (uart_regs->fr & ZYNQMP_FR_UART_BUSY);

    /* Disable the UART - UART must be disabled before control registers are reprogrammed. */
    // uart_regs->tcr &= ~(ZYNQMP_CR_RX_EN | ZYNQMP_CR_TX_EN | ZYNQMP_CR_UART_EN);

    /* Configure stop bit length to 1 */
    // uart_regs->lcr_h &= ~(ZYNQMP_LCR_2_STP_BITS);

    /* Set data length to 8 */
    // uart_regs->lcr_h |= (0b11 < ZYNQMP_LCR_WLEN_SHFT);

    /* Configure the reference clock and baud rate. Difficult to use automatic detection here as it requires the next incoming character to be 'a' or 'A'. */
    // set_baud(config.default_baud);

    /* Enable FIFOs */
    // uart_regs->lcr_h |= ZYNQMP_LCR_FIFO_EN;

    /* Disable parity checking */
    // uart_regs->lcr_h |= ZYNQMP_LCR_PARTY_EN;

    /* Enable receive interrupts when FIFO level exceeds 1/8 or after 32 ticks */
    /*
    if (config.rx_enabled) {
    sddf_dprintf("UART|LOG: Enabling RX 1st!\n");
        uart_regs->ifls &= ~(ZYNQMP_IFLS_RX_MASK << ZYNQMP_IFLS_RX_SHFT);
        uart_regs->imsc |= (ZYNQMP_IMSC_RX_TIMEOUT | ZYNQMP_IMSC_RX_INT);
    }
    */

    /* Enable transmit interrupts if the FIFO drops below 1/8 - used when the write fifo becomes full */
    // uart_regs->ifls &= ~(ZYNQMP_IFLS_TX_MASK << ZYNQMP_IFLS_TX_SHFT);
    // uart_regs->imsc |= ZYNQMP_IMSC_TX_INT;

    /* Enable the UART */
    // uart_regs->tcr |= ZYNQMP_CR_UART_EN;

    /* Enable transmit */
    // uart_regs->tcr |= ZYNQMP_CR_TX_EN;

    /* Enable receive */
    /*
    if (config.rx_enabled) {
        sddf_dprintf("UART|LOG: Enabling RX 2nd!\n");
        uart_regs->tcr |= ZYNQMP_CR_RX_EN;
    }
    */

    // NB! Below is JUNK.
    // Configure Line Control Register:
    // - 8-bit data length (WLEN = 11)
    // - Enable FIFO (FEN = 1)
    // - 1 stop bit, no parity
    // uart_regs->lcr_h = (1 << 4) | (1 << 5) | (1 << 6);

    // Enable UART, TX, and RX
    // uart_regs->tcr = (1 << 0) | (1 << 8) | (1 << 9);
}

void init(void)
{
    assert(serial_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    uart_regs = device_resources.regions[0].region.vaddr;

    uart_setup();

    if (config.rx_enabled) {
        serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    }
    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);
}

void notified(microkit_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        sddf_dprintf("UART|LOG: In NOTIFIED: handle_irq\n");
        handle_irq();
        microkit_deferred_irq_ack(ch);
    } else if (ch == config.tx.id) {
        sddf_dprintf("UART|LOG: In NOTIFIED: tx\n");
        tx_provide();
    } else if (ch == config.rx.id) {
        sddf_dprintf("UART|LOG: In NOTIFIED: rx\n");
        // FIXME: Enabling RX interrupt following ARM examine for UART.
        uart_regs->cr |= UART_CR_RX_EN;
        uart_regs->cr &= ~UART_CR_RX_DIS;
        rx_return();
    } else {
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
    }
}