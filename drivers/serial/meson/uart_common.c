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

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

volatile meson_uart_regs_t *uart_regs;
struct uart_clock_state uart_clock;

/* UART baud register expects baud rate to be expressed in terms of the number of reference
 ticks per symbol change. This function calculates these ticks and modifies the divisor of
 the reference clock accordingly. */
static void set_baud(unsigned long baud)
{
    /* Baud rate must be positive. */
    assert(baud > 0);

    uint64_t ref_clock_freq = uart_clock.reference_clock_frequency;
    uint64_t ref_clock_ticks_per_symbol = ref_clock_freq / baud;

    /* Check if baud rate can be acheived with a less frequent clock tick.
        Note: Linux defaults to use xtal div 3 if the board doesn't implement xtal_div2.
        They hardcode what boards support xtal_div2. This IS implemented on the odroidc4,
        but this may not work for different meson devices. */
    uint16_t clock_div = 1;
    uint32_t baud_register = AML_UART_BAUD_USE;
    if (uart_clock.crystal_clock) {
#if defined(CONFIG_PLAT_ODROIDC2)
        /* Odroid-C2 does not have clock divider option */
        baud_register |= AML_UART_BAUD_XTAL;
        clock_div = 3;
        ref_clock_ticks_per_symbol /= 3;
#elif defined(CONFIG_PLAT_ODROIDC4)
        baud_register |= AML_UART_BAUD_XTAL;
        if (ref_clock_ticks_per_symbol % 3 == 0) {
            clock_div = 3;
            ref_clock_ticks_per_symbol /= 3;
        } else if (ref_clock_ticks_per_symbol % 2 == 0) {
            clock_div = 2;
            ref_clock_ticks_per_symbol /= 2;
            baud_register |= AML_UART_BAUD_XTAL_DIV2;
        } else {
            baud_register |= AML_UART_BAUD_XTAL_DIV3;
        }
#endif
    }

    /* UART does not support baud rates this slow. */
    assert((ref_clock_ticks_per_symbol & ~AML_UART_BAUD_MASK) == 0);

    if (uart_clock.crystal_clock) {
        uart_clock.crystal_clock_divider = clock_div;
    }
    uart_clock.baud = baud;
    uart_clock.reference_ticks_per_symbol = ref_clock_ticks_per_symbol;
    baud_register |= ref_clock_ticks_per_symbol;
    uart_regs->reg5 = baud_register;
}

static void uart_setup(void)
{
    uart_regs = (meson_uart_regs_t *)device_resources.regions[0].region.vaddr;

    /* Wait until receive and transmit state machines are no longer busy */
    while (uart_regs->sr & (AML_UART_TX_BUSY | AML_UART_RX_BUSY));

    /* Disable transmit and receive */
    uart_regs->cr &= ~(AML_UART_TX_EN | AML_UART_RX_EN);

    /* Reset UART state machine */
    uart_regs->cr |= (AML_UART_TX_RST | AML_UART_RX_RST | AML_UART_CLEAR_ERR);
    uart_regs->cr &= ~(AML_UART_TX_RST | AML_UART_RX_RST | AML_UART_CLEAR_ERR);

    uint32_t cr = uart_regs->cr;
    /* Configure stop bit length to 1 */
    cr &= ~(AML_UART_STOP_BIT_LEN_MASK);
    cr |= AML_UART_STOP_BIT_1SB;

    /* Set data length to 8 */
    cr &= ~AML_UART_DATA_LEN_MASK;
    cr |= AML_UART_DATA_LEN_8BIT;

    /* Configure the reference clock and baud rate */
    uart_clock.crystal_clock = true;
    uart_clock.reference_clock_frequency = UART_XTAL_REF_CLK;
    uart_clock.crystal_clock_divider = 1;
    set_baud(config.default_baud);

    uint32_t irqc = uart_regs->irqc;
    /* Enable receive interrupts every byte */
    if (config.rx_enabled) {
        irqc &= ~AML_UART_RECV_IRQ_MASK;
        irqc |= AML_UART_RECV_IRQ(1);
        cr |= (AML_UART_RX_INT_EN | AML_UART_RX_EN);
    }

    /* Enable transmit interrupts if the write fifo drops below one byte - used when the write fifo becomes full */
    irqc &= ~AML_UART_XMIT_IRQ_MASK;
    irqc |= AML_UART_XMIT_IRQ(1);
    cr |= AML_UART_TX_EN;

    uart_regs->irqc = irqc;
    uart_regs->cr = cr;
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
