/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#define LOG_DRIVER(...) do{ sddf_dprintf("%s|INFO: ", microkit_name); sddf_dprintf(__VA_ARGS__); }while(0)
#define LOG_DRIVER_ERR(...) do{ sddf_dprintf("%s|ERROR: ", microkit_name); sddf_dprintf(__VA_ARGS__); }while(0)

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

#if defined(CONFIG_PLAT_STAR64)
/*  This reference clock value is taken from Pine64 u-boot.
    This value will be board specific. */
#define UART_CLK 24000000
#define UART_DW_APB_SHADOW_REGISTERS 1
#elif defined(CONFIG_PLAT_QEMU_RISCV_VIRT)
/* Obtained via the device tree that QEMU generates, and from
 * the QEMU source code.
 * https://github.com/qemu/qemu/blob/56c6e249b6988c1b6edc2dd34ebb0f1e570a1365/hw/riscv/virt.c#L966
 */
#define UART_CLK 3686400
#else
#error "unknown UART clock"
#endif

/* These register offsets are given as their offset in terms of reg-io-width;
 * e.g. for reg-io-width of 4 (32 bit accesses) the true offset for 0x1 is 0x4.
 * These drivers are also weird, as multiple registers are mapped to the same
 * memory and their access depends on the current state of the UART.
 */

/* UART Receive Buffer Register (R) */
#define UART_RBR 0x00

/* UART Transmit Holding Register (W) */
#define UART_THR 0x00

/* UART Divisor Low Latch Register (R/W) */
#define UART_DLL 0x00

/* UART Divisor High Latch Register (R/W) */
#define UART_DLH 0x01
/* Divisor Latch Mask */
#define DL_MASK 0xff

/* UART Interrupt Enable Register (R/W) */
#define UART_IER 0x01
/* Enable Received Data Available Interrupt */
#define UART_IER_ERBFI 0x1
/* Enable Transmit Holding Register Empty Interrupt */
#define UART_IER_ETBEI 0x2

/* UART Interrupt Identity Register (R) */
#define UART_IIR 0x02
/* Transmit Holding Register Empty */
#define UART_IIR_THR_EMPTY 0x2
/* Received Data Available */
#define UART_IIR_RX 0x4

/* UART FIFO Control Register (W) */
#define UART_FCR 0x02
/* Transmit FIFO Reset */
#define UART_FCR_XFIFOR (1 << 2)
/* Receive FIFO Reset */
#define UART_FCR_RFIFOR (1 << 1)
/* FIFO Enable */
#define UART_FCR_FIFOE (1 << 0)
/* FIFO Clear and Enable */
#define UART_FCR_CE (UART_FCR_XFIFOR | UART_FCR_RFIFOR | UART_FCR_FIFOE)

/* UART Line Control Register */
#define UART_LCR 0x03
/* Default for LCR. 8 bit data length and 2 stop bits*/
#define UART_LCR_DEFAULT 0x03
/* Divisor Latch Access Bit */
#define UART_LCR_DLAB (1 << 7)

/* UART Modem Control Register */
#define UART_MCR 0x4
/* Data Terminal Ready */
#define UART_MCR_DTR (1 << 0)
/* Request to Send */
#define UART_MCR_RTS (1 << 1)

/* UART Line Status Register (R) */
#define UART_LSR 0x05
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

/*
 * These registers are special to the DW APB UART implementation.
 */
#if defined(UART_DW_APB_SHADOW_REGISTERS)
/* UART Software Reset Register */
#define UART_SSR 0x22
/* UART Reset */
#define UART_SSR_UR (1 << 0)
#endif
