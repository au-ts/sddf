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
#include <os/sddf.h>
#include <sddf/util/util.h>
#include <sddf/serial/queue.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <sddf/serial/config.h>
#include <uart.h>

__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;
__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

bool waiting_for_tx_to_finish = false;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

/* UART device registers */
volatile uintptr_t uart_base;

#define REG_PTR(off)     ((volatile uint32_t *)(uart_base + off))

static void tx_provide(void)
{
    if (waiting_for_tx_to_finish) {
        /* Wait for TX FIFO empty IRQ before doing more work. */
        return;
    }

    bool transferred = false;
    char c;

    /* Send characters until the TX FIFO is full. */
    while (!(*REG_PTR(ZYNQMP_UART_SR) & ZYNQMP_UART_CHANNEL_STS_TXNFULL) && !serial_dequeue(&tx_queue_handle, &c)) {
        *REG_PTR(ZYNQMP_UART_FIFO) = (uint32_t)c;
        transferred = true;
    }

    if (transferred) {
        /* If work has been done, ensure that the TX FIFO empty IRQ status is cleared
         * as the status bits are sticky to prevent stray interrupts. */
        *REG_PTR(ZYNQMP_UART_ISR) = ZYNQMP_UART_IXR_TXEMPTY;
    }

    /* If there is more work to be done, raise a TX FIFO empty interrupt */
    if (!serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        *REG_PTR(ZYNQMP_UART_IER) = ZYNQMP_UART_IXR_TXEMPTY;
        waiting_for_tx_to_finish = true;
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
        /* Read from RX FIFO until it is empty. */
        while (!(*REG_PTR(ZYNQMP_UART_SR) & ZYNQMP_UART_CHANNEL_STS_RXEMPTY)
               && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            char c = *REG_PTR(ZYNQMP_UART_FIFO);
            serial_enqueue(&rx_queue_handle, c);
            enqueued = true;
        }

        if (!(*REG_PTR(ZYNQMP_UART_SR) & ZYNQMP_UART_CHANNEL_STS_RXEMPTY)
            && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            /* There's still data to receive but the RX queue is full. */
            serial_request_consumer_signal(&rx_queue_handle);
        }
        reprocess = false;

        if (!(*REG_PTR(ZYNQMP_UART_SR) & ZYNQMP_UART_CHANNEL_STS_RXEMPTY)
            && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            /* There's more space available in the queue. */
            serial_cancel_consumer_signal(&rx_queue_handle);
            reprocess = true;
        }
    }

    if (enqueued) {
        sddf_notify(config.rx.id);
    }
}

static void handle_irq(void)
{
    /* Read and clear the IRQ status bits so we don't get infinitely interrupted. */
    uint32_t irq_status = *REG_PTR(ZYNQMP_UART_ISR);
    *REG_PTR(ZYNQMP_UART_ISR) = irq_status;

    if (irq_status & ZYNQMP_UART_IXR_TXEMPTY) {
        /* We previously requested the device to raise an IRQ when the TX FIFO is empty because it became full
           while doing work, now continue. */
        waiting_for_tx_to_finish = false;

        /* Make sure the status register is consistent with our programming model.
         * If you use your OS' debug print that bypasses this driver, this assert will trip. */
        assert(*REG_PTR(ZYNQMP_UART_SR) & ZYNQMP_UART_IXR_TXEMPTY);

        /* Switch off the TX FIFO empty IRQ, only turn it on again when needed. */
        *REG_PTR(ZYNQMP_UART_IDR) = ZYNQMP_UART_IXR_TXEMPTY;

        /* Continue sending data from sDDF queue. */
        tx_provide();
    }
    if (irq_status & ZYNQMP_UART_IXR_RXOVR) {
        /* The RX FIFO level has hit the watermark, in this case it is 1 byte. Process RX FIFO. */
        assert(!(*REG_PTR(ZYNQMP_UART_SR) & ZYNQMP_UART_IXR_RXEMPTY));
        rx_return();
    }
}

static void compute_clk_divs(uint64_t clock_hz, uint64_t baudrate, uint16_t *cd, uint8_t *bdiv)
{
    /* Page 589 of TRM

    Baud rate = sel_clk / (CD * (BDIV + 1))

    This function's goal is to calculate the CD and BDIV values for setting the baud rate. Where:
        sel_clk = clock_hz
        CD      = baud rate generator divisor value
        BDIV    = baud rate divider value

    CD is used to derive the baud sample rate
    CD and BDIV are used to derive the RX and TX baud rate.

    BDIV can be programmed with a value between 4 and 255.
    For the target bps, solve for the optimal baudgen divider (CD).
    Take the first result that is <3% in error. So:

    sel_clk = baud * (CD * (BDIV + 1))
    CD * (BDIV + 1) = sel_clk / baud
    CD = (sel_clk / baud) / (BDIV + 1)
    */

    uint64_t computed_bdiv = ZYNQMP_UART_BDIV_MIN;
    uint64_t computed_cd = 0;
    double acceptable_error_rate = 0.03;
    for (; computed_bdiv <= ZYNQMP_UART_BDIV_MAX; computed_bdiv++) {
        uint64_t guessed_cd = (clock_hz / (baudrate * 1.0)) / (computed_bdiv + 1);

        /* If CD yields 0 or 1, go to the next possible BDIV because those are
           reserved values. Register references, UG1087: "Baud_rate_gen (UART) Register Description"
         */
        if (guessed_cd < ZYNQMP_UART_CD_MIN) {
            continue;
        }

        /* Now solve the equation. */
        double actual_baud = clock_hz / ((guessed_cd * (computed_bdiv + 1)) * 1.0);

        double difference = ABS(actual_baud - baudrate);
        double error_rate = difference / baudrate;
        if (error_rate < acceptable_error_rate) {
            computed_cd = guessed_cd;
            break;
        }
    }

    /* Should never trip, unless your uart clock or baud rate are incorrect */
    assert(computed_cd >= ZYNQMP_UART_CD_MIN && computed_cd <= ZYNQMP_UART_CD_MAX);

    *cd = (uint16_t)computed_cd;
    *bdiv = (uint8_t)computed_bdiv;
}

static void tx_fifo_drain_wait(void)
{
    /* Wait for the TX FIFO to drain. */
    while (!(*REG_PTR(ZYNQMP_UART_SR) & ZYNQMP_UART_CHANNEL_STS_TXEMPTY));
    /* Wait for the Transmitter to finish sending the signals. */
    while ((*REG_PTR(ZYNQMP_UART_SR) & ZYNQMP_UART_CHANNEL_STS_TXACTIVE));
}

static void uart_setup(void)
{
    /* Wait for any previous UART access to complete before we reset the serial device. */
    tx_fifo_drain_wait();

    /* Compute the correct clock dividers to set the baud rate. */
    uint16_t cd;
    uint8_t bdiv;
    compute_clk_divs(ZYNQMP_UART_REF_CLOCK_RATE, config.default_baud, &cd, &bdiv);

    /* Disable TX and RX before the UART registers can be reprogrammed (page 589).
     * First clear the enable bit then set the disabled bit.
     */
    uint32_t cr = *REG_PTR(ZYNQMP_UART_CR);
    cr &= ~((uint32_t)(BIT(ZYNQMP_UART_CR_TX_EN_SHIFT) | BIT(ZYNQMP_UART_CR_RX_EN_SHIFT)));
    cr |= ZYNQMP_UART_CR_TX_DIS | ZYNQMP_UART_CR_RX_DIS;
    *REG_PTR(ZYNQMP_UART_CR) = cr;

    /* Clear the mode register to make sure the device is operating in normal mode
     * and the clock isn't divided by 8 */
    *REG_PTR(ZYNQMP_UART_MR) = 0;

    /* Set the baud rate by programming the clock dividers */
    *REG_PTR(ZYNQMP_UART_BAUDDIV) = bdiv;
    *REG_PTR(ZYNQMP_UART_BAUDGEN) = cd;

    /* Reset TX and RX and wait for the reset to complete. */
    *REG_PTR(ZYNQMP_UART_CR) |= ZYNQMP_UART_CR_TX_RST | ZYNQMP_UART_CR_RX_RST;
    while (*REG_PTR(ZYNQMP_UART_CR) & (ZYNQMP_UART_CR_TX_RST | ZYNQMP_UART_CR_RX_RST));

    /* Clear the TX and RX disable bit. */
    cr = *REG_PTR(ZYNQMP_UART_CR);
    cr &= ~((uint32_t)(BIT(ZYNQMP_UART_CR_TX_DIS_SHIFT) | BIT(ZYNQMP_UART_CR_RX_DIS_SHIFT)));

    /* Enable TX and RX. */
    cr |= ZYNQMP_UART_CR_TX_EN | ZYNQMP_UART_CR_RX_EN;
    *REG_PTR(ZYNQMP_UART_CR) = cr;

    /* Select 8 bytes character length. */
    uint32_t mr = *REG_PTR(ZYNQMP_UART_MR);
    mr &= ~((BIT(0) | BIT(1)) << ZYNQMP_UART_MR_CHARLEN_SHIFT);

    /* No parity checks */
    mr |= ZYNQMP_UART_MR_PARITY_NONE;

    /* One stop bit to detect on RX and to generate on TX */
    mr &= ~((BIT(0) | BIT(1)) << ZYNQMP_UART_MR_STOPMODE_SHIFT);

    /* Put the UART device in normal operating mode */
    mr &= ~((BIT(0) | BIT(1)) << ZYNQMP_UART_MR_CHMODE_SHIFT);
    *REG_PTR(ZYNQMP_UART_MR) = mr;

    /* Turn off all the interrupts, then only turn on the ones we need. */
    *REG_PTR(ZYNQMP_UART_IDR) = ZYNQMP_UART_IXR_MASK;
    *REG_PTR(ZYNQMP_UART_ISR) = ZYNQMP_UART_IXR_MASK;

    if (config.rx_enabled) {
        /* Set the watermark to raise an interrupt for every received byte. */
        *REG_PTR(ZYNQMP_UART_RXWM) = 1;

        /* Enable IRQ on every bytes received. */
        *REG_PTR(ZYNQMP_UART_IER) = ZYNQMP_UART_IXR_RXOVR;
    }
}

void init(void)
{
    assert(serial_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    /* Ack any IRQs that were delivered before the driver started. */
    sddf_irq_ack(device_resources.irqs[0].id);

    uart_base = (uintptr_t)device_resources.regions[0].region.vaddr;
    uart_setup();

    if (config.rx_enabled) {
        serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    }
    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);
}

void notified(sddf_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();
        sddf_deferred_irq_ack(ch);
    } else if (ch == config.tx.id) {
        tx_provide();
    } else if (ch == config.rx.id) {
        rx_return();
    } else {
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
    }
}
