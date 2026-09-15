/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <uart.h>

__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

/* UART device registers */
volatile uintptr_t uart_base;

static void set_baud(unsigned long baud)
{
    /*  Divisor Latch Access Bit (DLAB) of the LCR must be set.
    *   These registers share their address with the FIFO's.
    */
#if UART_DW_APB_REGISTERS
    /*
     * From the specification for DLH:
     * "This register may only be accessed when the DLAB bit (LCR[7]) is set
     * and the UART is not busy (USR[0] is zero)"
     */
    while (*REG_PTR(UART_USR) & UART_USR_BUSY);
#endif

    uint32_t lcr_val = *REG_PTR(UART_LCR);

    *REG_PTR(UART_LCR) |= UART_LCR_DLAB;

    /* baud rate = (serial_clock_freq) / (16 * divisor) */
    uint16_t divisor = DIV_ROUND_CLOSEST(UART_CLK, 16 * baud);

    *REG_PTR(UART_DLH) = (divisor >> 8) & 0xff;
    *REG_PTR(UART_DLL) = divisor & 0xff;

    /* Restore the LCR */
    *REG_PTR(UART_LCR) = lcr_val;
}

void init(void)
{
    assert(serial_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    uart_base = (uintptr_t)device_resources.regions[0].region.vaddr;

    /* Ensure that the FIFO's are empty */
    while (~(*REG_PTR(UART_LSR)) & (UART_LSR_THRE | UART_LSR_TEMT));

    /* Disable all interrupts for now */
    *REG_PTR(UART_IER) = 0;

    /* Clear any error indication bits */
    (void)*REG_PTR(UART_LSR);
    /* Reset interrupt indications. */
    (void)*REG_PTR(UART_IIR);

    /* Setup the Modem Control Register */
    *REG_PTR(UART_MCR) = (UART_MCR_DTR | UART_MCR_RTS);

    /* Reset and enable the FIFO's*/
    *REG_PTR(UART_FCR) = (UART_FCR_XFIFOR | UART_FCR_RFIFOR | UART_FCR_FIFOE);

    /* Set LCR format; 8 bit data length (bits 0-1), 1 stop bit (bit 2),
       no parity, no break control. */
    *REG_PTR(UART_LCR) = 0b00000011;

    /* Set the baud rate */
    set_baud(config.default_baud);

    if (config.rx_enabled) {
        /* Enable (only) the receive data available IRQ
           -> TX enabled as needed by tx_provide(). */
        *REG_PTR(UART_IER) = UART_IER_ERBFI;

        serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    }

    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);

#if UART_DW_APB_REGISTERS
    /* Clear the USR busy bit
     * This must be done after enabling IRQs
     * https://github.com/torvalds/linux/blob/v6.14/drivers/tty/serial/8250/8250_dw.c#L304-L306
     */
    (void)*REG_PTR(UART_USR);
#endif

    post_init();
}
