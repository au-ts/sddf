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

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

volatile imx_uart_regs_t *uart_regs;

/*
 * BaudRate = RefFreq / (16 * (BMR + 1)/(BIR + 1) )
 * RefFreq = module clock after divider is applied.
 * Set BIR to 15 for integer division.
 * BMR and BIR are 16 bit.
 */
static void set_baud(long bps)
{
    uint32_t bmr, bir, fcr;
    fcr = uart_regs->fcr;
    fcr &= ~UART_FCR_REF_FRQ_DIV_MSK;
    fcr |= UART_FCR_REF_CLK_DIV_2;
    bir = 0xf;
    bmr = (UART_MOD_CLK / 2) / bps - 1;
    uart_regs->fcr = fcr;
    uart_regs->bir = bir;
    uart_regs->bmr = bmr;
}

static void uart_setup(void)
{
    uart_regs = (imx_uart_regs_t *)device_resources.regions[0].region.vaddr;

    /* Enable the UART */
    uart_regs->cr1 |= UART_CR1_UART_EN;

    /* Enable transmit and receive */
    uart_regs->cr2 |= UART_CR2_TX_EN;
    if (config.rx_enabled) {
        uart_regs->cr2 |= UART_CR2_RX_EN;
    }

    /* Configure stop bit length to 1 */
    uart_regs->cr2 &= ~(UART_CR2_STOP_BITS);

    /* Set data length to 8 */
    uart_regs->cr2 |= UART_CR2_WORD_SZE;

    /* Configure the reference clock and baud rate. Difficult to use automatic detection here as it requires the next incoming character to be 'a' or 'A'. */
    set_baud(config.default_baud);

    /* Disable escape sequence, parity checking and aging rx data interrupts. */
    uart_regs->cr2 &= ~UART_CR2_PARITY_EN;
    uart_regs->cr2 &= ~(UART_CR2_ESCAPE_EN | UART_CR2_ESCAPE_INT);
    uart_regs->cr2 &= ~UART_CR2_AGE_EN;

    uint32_t fcr = uart_regs->fcr;
    /* Enable receive interrupts every byte */
    if (config.rx_enabled) {
        fcr &= ~UART_FCR_RXTL_MASK;
        fcr |= (1 << UART_FCR_RXTL_SHFT);
    }

    /* Enable transmit interrupts if the write fifo drops below one byte - used when the write fifo becomes full */
    fcr &= ~UART_FCR_TXTL_MASK;
    fcr |= (2 << UART_FCR_TXTL_SHFT);

    uart_regs->fcr = fcr;
    if (config.rx_enabled) {
        uart_regs->cr1 |= UART_CR1_RX_READY_INT;
    }
}

void init(void)
{
    assert(serial_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    uart_setup();

    if (config.rx_enabled) {
        serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    }
    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);

    post_init();
}
