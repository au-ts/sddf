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
#define UART_DW_APB_REGISTERS 1
#elif defined(CONFIG_PLAT_NANOPI_R5C)
#define UART_CLK 0x16e3600
#define UART_DW_APB_REGISTERS 1
#elif defined(CONFIG_PLAT_QEMU_RISCV_VIRT)
/* Obtained via the device tree that QEMU generates, and from
 * the QEMU source code.
 * https://github.com/qemu/qemu/blob/56c6e249b6988c1b6edc2dd34ebb0f1e570a1365/hw/riscv/virt.c#L966
 */
#define UART_CLK 3686400
#define UART_DW_APB_REGISTERS 0
#elif defined(CONFIG_PLAT_CHESHIRE)
#define UART_CLK 50000000
#define UART_DW_APB_REGISTERS 0
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

/* UART Interrupt Enable Register (R/W) */
#define UART_IER 0x01
/* Enable Received Data Available Interrupt, if FIFOs are enabled, the
 * Character Timeout Interrupt. */
#define UART_IER_ERBFI BIT(0)
/* Enable Transmit Holding Register Empty Interrupt */
#define UART_IER_ETBEI BIT(1)

/* UART Interrupt Identity Register (R) */
#define UART_IIR 0x02
/* Interrupt ID Mask.
 * According to the DW_APB_UART manual, this is bits 3:0, i.e. should be 0b1111
 * The UART_IER_ERBFI (received data available interrupt) also enables the
 * character timeout interrupt, i.e. 0b1100 for the IID.
 * Furthermore, the manual specifies that the priorities put the received data
 * interrupt *above* the character timeout interrupt.
 *
 * However, QEMU seems to disagree, and places the timeout interrupt above the
 * received data interrupt.
 *
 * It appears that Zephyr just ignores it, which seems suspicious. But so does
 * Linux.
 *
 * ??
 */
#define UART_IIR_IID_MASK (0b0111)
/* Interrupt ID = Transmit Holding Register Indicator */
#define UART_IIR_IID_THRI (0b0010)
/* Interrupt ID = Received Data Available */
#define UART_IIR_IID_RDI (0b0100)

/* UART FIFO Control Register (W) */
#define UART_FCR 0x02
/* FIFO Enable */
#define UART_FCR_FIFOE BIT(0)
/* Receive FIFO Reset */
#define UART_FCR_RFIFOR BIT(1)
/* Transmit FIFO Reset */
#define UART_FCR_XFIFOR BIT(2)

/* UART Line Control Register (RW) */
#define UART_LCR 0x03
/* Divisor Latch Access Bit */
#define UART_LCR_DLAB BIT(7)

/* UART Modem Control Register (RW) */
#define UART_MCR 0x4
/* Data Terminal Ready */
#define UART_MCR_DTR BIT(0)
/* Request to Send */
#define UART_MCR_RTS BIT(1)

/* UART Line Status Register (R) */
#define UART_LSR 0x05
/* Data Ready */
#define UART_LSR_DR BIT(0)
/* Parity Error Bit */
#define UART_LSR_PE BIT(2)
/* Framing Error Bit */
#define UART_LSR_FE BIT(3)
/* Transmit Holding Register Empty */
#define UART_LSR_THRE BIT(5)
/* Transmit FIFO and Transmit Shift register Empty */
#define UART_LSR_TEMT BIT(6)
/* Recv FIFO Error Bit */
#define UART_LSR_RFE BIT(7)

/*
 * These registers are special to the DW APB UART implementation.
 */
#if UART_DW_APB_REGISTERS
/* UART Software Reset Register */
#define UART_SSR 0x22
/* UART Reset */
#define UART_SSR_UR BIT(0)

/* UART Status Register (0x7C >> 2 = 0x1f) */
#define UART_USR 0x1f
/* UART BUSY */
#define UART_USR_BUSY BIT(0)
/* Transmit FIFO Not Full */
#define UART_USR_TFNF BIT(1)
#endif
