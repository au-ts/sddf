/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Documents referenced: Zynq UltraScale+ Device TRM, UG1085 (v2.5) March 21, 2025.
 *                       Zynq UltraScale+ Devices Register Reference (UG1087) 
 * U-Boot driver referenced: https://github.com/u-boot/u-boot/blob/master/drivers/serial/serial_zynq.c
 * Linux driver referenced:  https://github.com/torvalds/linux/blob/master/drivers/tty/serial/xilinx_uartps.c
 *
 * All page referenced will be in terms of the TRM unless otherwise stated.
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <sddf/serial/config.h>
// #include <uart.h>
#include "include/uart.h"

__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;
__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

volatile zynqmp_uart_regs_t *uart_regs;

static void tx_provide(void)
{
    bool transferred = false;
    char c;

    /* Wait for the TX FIFO to drain before sending anything. */
    while (!(uart_regs->sr & ZYNQMP_UART_CHANNEL_STS_TXFULL) && !serial_dequeue(&tx_queue_handle, &c)) {
        uart_regs->fifo = (uint8_t) c;
        /* Wait for the data to shift out */
        while (uart_regs->sr & ZYNQMP_UART_CHANNEL_STS_TXACTIVE);
        transferred = true;
    }

    /* Serial queue should be completely empty. */
    assert(serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head));

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
        while (!(uart_regs->sr & ZYNQMP_UART_CHANNEL_STS_RXEMPTY)
               && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            char c = (uint32_t)(uart_regs->fifo);
            sddf_dprintf("got %c\n", c);
            serial_enqueue(&rx_queue_handle, c);
            enqueued = true;
        }

        if (!(uart_regs->sr & ZYNQMP_UART_CHANNEL_STS_RXEMPTY) && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            /* There's still data to receive but the RX queue is full. */
            serial_request_consumer_signal(&rx_queue_handle);
        }
        reprocess = false;

        if (!(uart_regs->sr & ZYNQMP_UART_CHANNEL_STS_RXEMPTY) && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            /* Oh wait, there's space available in the queue. */
            serial_cancel_consumer_signal(&rx_queue_handle);
            reprocess = true;
        }
    }

    if (enqueued) {
        microkit_notify(config.rx.id);
    }
}

static void handle_irq(void)
{
    uint32_t prev = uart_regs->imr;
    sddf_printf("int mask is %x, c_sts is %x\n", prev, uart_regs->sr);
    uart_regs->idr = 0x1FFF;
    rx_return();
    uart_regs->ier = prev;
}

static void compute_clk_divs(uint64_t clock_hz, uint64_t baudrate, uint16_t *cd, uint8_t *bdiv)
{
    /* Page 589 of TRM

    Baud rate = sel_clk / (CD * (BDIV + 1))
    
    This function's goal is to calculate and set CD and BDIV. Where:
        sel_clk = clock_hz
        CD      = baud rate generator divisor value
        BDIV    = baud rate divider value

    CD is used to derive the baud sample rate
    CD and BDIV are used to derive the RX and TX baud rate.

    */

    /* BDIV can be programmed with a value between 4 and 255.
       For the target bps, solve for the optimal baudgen divider (CD).
       Take the first result that is <1% in error. So:

       sel_clk = baud * (CD * (BDIV + 1))
       CD * (BDIV + 1) = sel_clk / baud
       CD = (sel_clk / baud) / (BDIV + 1)
       
       The U-Boot and Linux drivers take anything <3% in error. But the data sheet
       shows that we can achieve <0.5% error for all common baud settings
       so taking <1% in our driver.
    */

    /* Page 588, bdiv is 16 bits wide, cd is 8 bits */
    uint16_t computed_bdiv = 4;
    uint16_t computed_cd = 0;
    double acceptable_error_rate = 0.01;
    for (; computed_bdiv <= 255; computed_bdiv++) {
        computed_cd = (clock_hz / (baudrate * 1.0)) / (computed_bdiv + 1);

        /* If CD yields 0 or 1, go to the next possible BDIV because those are
           reserved values. Register references, UG1087: "Baud_rate_gen (UART) Register Description"
         */
        if (computed_cd == 0 || computed_cd == 1) {
            continue;
        }

        /* Now solve the equation. */
        double actual_baud = clock_hz / ((computed_cd * (computed_bdiv + 1)) * 1.0);

        /* Check error rate, take first result <1% error. */
        double difference = ABS(actual_baud - baudrate);
        double error_rate = difference / baudrate;
        
        if (error_rate < acceptable_error_rate) {
            break;
        }
    }

    /* Should never trips, unless your uart clock or baud rate are incorrect */
    assert(computed_cd != 0 && computed_bdiv < 255);

    *cd = computed_cd;
    *bdiv = (uint8_t) computed_bdiv;
}

static void uart_setup(void)
{
    sddf_printf("uboot cd = %u, bdiv = %u\n", uart_regs->baudgen, uart_regs->bauddiv);

    uint16_t cd;
    uint8_t bdiv;
    compute_clk_divs(100 * 1000 * 1000, config.default_baud, &cd, &bdiv);

    sddf_printf("our cd = %u, bdiv = %u\n", cd, bdiv);

    /* Disable TX and RX before the UART registers can be reprogrammed (star at page 589).
     * First clear the enable bit then set the disabled bit.
     */
    uint32_t cr = uart_regs->cr;
    cr &= ~((uint32_t) (BIT(ZYNQMP_UART_CR_TX_EN_SHIFT) | BIT(ZYNQMP_UART_CR_RX_EN_SHIFT)));
    cr |= ZYNQMP_UART_CR_TX_DIS | ZYNQMP_UART_CR_RX_DIS;
    uart_regs->cr = cr;

    /* Program the clock dividers */
    uart_regs->bauddiv = bdiv;
    uart_regs->baudgen = cd;

    /* Reset TX and RX. */
    uart_regs->cr |= ZYNQMP_UART_CR_TX_RST | ZYNQMP_UART_CR_RX_RST;
    while (uart_regs->cr & (ZYNQMP_UART_CR_TX_RST | ZYNQMP_UART_CR_RX_RST));

    /* Clear the TX and RX disable bit. */
    cr = uart_regs->cr;
    cr &= ~((uint32_t) (BIT(ZYNQMP_UART_CR_TX_DIS_SHIFT) | BIT(ZYNQMP_UART_CR_RX_DIS_SHIFT)));

    /* Enable TX and RX. */
    cr |= ZYNQMP_UART_CR_TX_EN | ZYNQMP_UART_CR_RX_EN;
    uart_regs->cr = cr;

    /* Select 8 bytes character length. */
    uint32_t mr = uart_regs->mr;
    mr &= ~(0x3 << ZYNQMO_UART_MR_CHARLEN_SHIFT);

    /* Make sure the input clock isn't divided by 8. */
    mr |= ZYNQMO_UART_MR_CHMODE_NORM;

    /* No parity checks */
    mr |= ZYNQMO_UART_MR_PARITY_NONE;

    /* One stop bit to detect on RX and to generate on TX */
    mr &= ~(0x3 << ZYNQMO_UART_MR_STOPMODE_SHIFT);

    /* Put the UART device in normal operating mode */
    mr &= ~(0x3 << ZYNQMO_UART_MR_CHMODE_SHIFT);
    uart_regs->mr = mr;

    /* Turn off all the interrupts, then only turn on the ones we need. */
    uart_regs->idr = 0xFFFF;

    if (config.rx_enabled) {
        /* Generate an interrupt for every received byte. */
        uart_regs->rxwm = 1;

        /* Enable IRQ on every bytes received. */
        uart_regs->ier |= ZYNQMO_UART_IXR_RXOVR;
    }
    sddf_dprintf("UART|LOG: Initialised UART!\n");
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
        tx_provide();
    } else if (ch == config.rx.id) {
        rx_return();
    } else {
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
    }
}