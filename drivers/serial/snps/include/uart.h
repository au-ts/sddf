/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#define LOG_DRIVER(...) do{ microkit_dbg_puts(microkit_name); microkit_dbg_puts("|INFO: "); microkit_dbg_puts(__VA_ARGS__); }while(0)
#define LOG_DRIVER_ERR(...) do{ microkit_dbg_puts(microkit_name); microkit_dbg_puts("|ERROR: "); microkit_dbg_puts(__VA_ARGS__); }while(0)

/*
 * Divide positive or negative dividend by positive divisor and round
 * to closest integer. Result is undefined for negative divisors and
 * for negative dividends if the divisor variable type is unsigned.
 */
#define DIV_ROUND_CLOSEST(x, divisor)(          \
{                           \
    typeof(x) __x = x;              \
    typeof(divisor) __d = divisor;          \
    (((typeof(x))-1) > 0 ||             \
     ((typeof(divisor))-1) > 0 || (__x) > 0) ?  \
        (((__x) + ((__d) / 2)) / (__d)) :   \
        (((__x) - ((__d) / 2)) / (__d));    \
}                           \
)

/*  This reference clock value is taken from Pine64 u-boot.
    This value will be board specific. */
#define UART_CLK 24000000

/* UART Receive Buffer Register */
#define UART_RBR 0x00
/* UART Transmit Holding Register */
#define UART_THR 0x00
/* UART Interrupt Enable Register */
#define UART_IER 0x04
/* UART Interrupt Identity Register */
#define UART_IIR 0x08
/* Transmit Holding Register Empty */
#define UART_IIR_THR_EMPTY 0x2
/* Received Data Available */
#define UART_IIR_RX 0x4
/* Enable Received Data Available Interrupt */
#define UART_IER_ERBFI 0x1
/* Enable Transmit Holding Register Empty Interrupt */
#define UART_IER_ETBEI 0x2
/* UART Line Status Register */
#define UART_LSR 0x14
/* Data Ready */
#define UART_LSR_DR 0x1
/* Transmit Holding Register Empty */
#define UART_LSR_THRE 0x20
/* Parity Error Bit */
#define UART_LSR_PE (1 << 2)
/* Framing Error Bit */
#define UART_LSR_FE (1 << 3)
/* Recv FIFO Error Bit */
#define UART_LSR_RFE (1 << 7)
/* Abnormal Status */
#define UART_ABNORMAL (UART_LSR_PE | UART_LSR_FE | UART_LSR_RFE)
/* UART Software Reset Register */
#define UART_SSR 0x88
/* UART Reset */
#define UART_SSR_UR (1 << 0)
/* UART Modem Control Register */
#define UART_MCR 0x10
/* Data Terminal Ready */
#define UART_MCR_DTR (1 << 0)
/* Request to Send */
#define UART_MCR_RTS (1 << 1)
/* UART FIFO Control Register NOTE - This is the same offset as
the IIR, but the IIR is read-only, and the FCR is write-only. */
#define UART_FCR 0x08
/* Transmit FIFO Reset */
#define UART_FCR_XFIFOR (1 << 2)
/* Receive FIFO Reset */
#define UART_FCR_RFIFOR (1 << 1)
/* FIFO Enable */
#define UART_FCR_FIFOE (1 << 0)
/* FIFO Clear and Enable */
#define UART_FCR_CE (UART_FCR_XFIFOR | UART_FCR_RFIFOR | UART_FCR_FIFOE)
/* UART Line Control Register */
#define UART_LCR 0x0C
/* Default for LCR. 8 bit data length and 2 stop bits*/
#define UART_LCR_DEFAULT 0x03
/* Divisor Latch Access Bit */
#define UART_LCR_DLAB (1 << 7)
/* UART Divisor High Latch */
#define UART_DLH 0x04
/* UART Divisor Low Latch */
#define UART_DLL 0x00
/* Divisor Latch Mask */
#define DL_MASK 0xff