/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <sddf/resources/device.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>

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

extern __attribute__((__section__(".device_resources"))) device_resources_t device_resources;
extern __attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

extern serial_queue_handle_t rx_queue_handle;
extern serial_queue_handle_t tx_queue_handle;

extern void write(uint16_t port_offset, uint8_t v);
extern uint8_t read(uint16_t port_offset);

extern void post_init();
