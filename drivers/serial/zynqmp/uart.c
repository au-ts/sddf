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

bool waiting_for_tx_to_finish = false;

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

void post_init()
{
}
