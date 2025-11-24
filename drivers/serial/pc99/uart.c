/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>
#include <sddf/resources/device.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

// @billn Need a way to express io port in sdfgen config structure
#define IOPORT_ID 0
#define IOPORT_BASE 0x3f8
// @billn need some sort of "machine description" format for x86 sdfgen to automatically pull in IRQ
#define IRQ_ID 1

/*
 * Port offsets
 * W    - write
 * R    - read
 * RW   - read and write
 * DLAB - Alternate register function bit
 */

#define SERIAL_THR  0 /* Transmitter Holding Buffer (W ) DLAB = 0 */
#define SERIAL_RBR  0 /* Receiver Buffer            (R ) DLAB = 0 */
#define SERIAL_DLL  0 /* Divisor Latch Low Byte     (RW) DLAB = 1 */
#define SERIAL_IER  1 /* Interrupt Enable Register  (RW) DLAB = 0 */
#define SERIAL_DLH  1 /* Divisor Latch High Byte    (RW) DLAB = 1 */
#define SERIAL_IIR  2 /* Interrupt Identification   (R ) */
#define SERIAL_FCR  2 /* FIFO Control Register      (W ) */
#define SERIAL_LCR  3 /* Line Control Register      (RW) */
#define SERIAL_MCR  4 /* Modem Control Register     (RW) */
#define SERIAL_LSR  5 /* Line Status Register       (R ) */
#define SERIAL_MSR  6 /* Modem Status Register      (R ) */
#define SERIAL_SR   7 /* Scratch Register           (RW) */
#define SERIAL_DLAB BIT(7)
#define SERIAL_LSR_DATA_READY BIT(0)
#define SERIAL_LSR_TRANSMITTER_EMPTY BIT(5)

enum irq_state { MODEM_STATUS = 0, TX_HOLD_REG_EMPTY, RX_DATA_AVAIL, RX_LINE_STS };

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

void write(uint16_t port_offset, uint8_t v)
{
    microkit_x86_ioport_write_8((IOPORT_ID), IOPORT_BASE + port_offset, v);
}

uint8_t read(uint16_t port_offset)
{
    return microkit_x86_ioport_read_8((IOPORT_ID), IOPORT_BASE + port_offset);
}

int tx_ready(void)
{
    return read(SERIAL_LSR) & SERIAL_LSR_TRANSMITTER_EMPTY;
}

int rx_ready(void)
{
    return read(SERIAL_LSR) & SERIAL_LSR_DATA_READY;
}

void init(void)
{
    assert(serial_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));

    if (config.rx_enabled) {
        serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    }
    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);

    while (!(read(SERIAL_LSR) & 0x60)); /* wait until not busy */

    write(SERIAL_LCR, 0x00); /* line control register: command: set divisor */
    if (config.rx_enabled) {
        write(SERIAL_IER, 0x01); /* IRQ on received data available */
    } else {
        write(SERIAL_IER, 0x00); /* disable generating interrupts */
    }
    write(SERIAL_LCR, 0x80); /* line control register: command: set divisor */
    write(SERIAL_DLL, 0x01); /* set low byte of divisor to 0x01 = 115200 baud */
    write(SERIAL_DLH, 0x00); /* set high byte of divisor to 0x00 */
    write(SERIAL_LCR, 0x03); /* line control register: set 8 bit, no parity, 1 stop bit */
    write(SERIAL_MCR, 0x0b); /* modem control register: set DTR/RTS/OUT2 */
    write(SERIAL_FCR, 0x00); /* set IRQ trigger level to 1 byte */

    read(SERIAL_RBR); /* clear receiver port */
    read(SERIAL_LSR); /* clear line status port */
    read(SERIAL_MSR); /* clear modem status port */
}

static void tx_provide(void)
{
    bool transferred = false;
    char c;
    while (!serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        serial_dequeue(&tx_queue_handle, &c);
        while (!tx_ready());
        write(SERIAL_THR, c);
        transferred = true;
    }

    if (transferred && serial_require_consumer_signal(&tx_queue_handle)) {
        serial_cancel_consumer_signal(&tx_queue_handle);
        microkit_notify(config.tx.id);
    }
}

static void rx_return(void)
{
    bool enqueued = false;
    while (rx_ready() && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
        char c = (char)read(SERIAL_RBR);
        serial_enqueue(&rx_queue_handle, c);
        enqueued = true;
    }

    if (enqueued) {
        microkit_notify(config.rx.id);
    }
}

static void handle_irq(void)
{
    uint8_t iir = read(SERIAL_IIR) >> 1;
    if (iir & RX_DATA_AVAIL) {
        rx_return();
    }
}

void notified(microkit_channel ch)
{
    if (ch == config.tx.id) {
        tx_provide();
    } else if (ch == config.rx.id) {
        rx_return();
    } else if (ch == IRQ_ID) {
        handle_irq();
        microkit_deferred_irq_ack(IRQ_ID);
    } else {
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
    }
}
