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

__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

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

static void uart_setup(void)
{
    /* Wait for UART to finish transmitting. */
    while (uart_regs->fr & PL011_FR_UART_BUSY);

    /* Disable the UART - UART must be disabled before control registers are reprogrammed. */
    uart_regs->tcr &= ~(PL011_CR_RX_EN | PL011_CR_TX_EN | PL011_CR_UART_EN);

    /* Configure stop bit length to 1 */
    uart_regs->lcr_h &= ~(PL011_LCR_2_STP_BITS);

    /* Set data length to 8 */
    uart_regs->lcr_h |= (0b11 << PL011_LCR_WLEN_SHFT);

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

    post_init();
}
