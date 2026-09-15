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
#include <uart.h>

// TODO: the retain and used attributes are necessary as nothing uses/refers to this section
// in release mode in this driver.
// The solution is to fix our tooling to generate device resources for this driver as well
// and then remove 'retain,used'.
__attribute__((__section__(".device_resources"), retain, used)) device_resources_t device_resources;
__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

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

    post_init();
}
