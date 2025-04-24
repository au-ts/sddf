/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <sddf/util/util.h>
#include <sddf/serial/queue.h>

/*
* The various constant definitions for xuart are from Xilinx BSP
* source code for Zynqmp.
*/

// These were all sourced from Xilinx BSP for zynqmp. Not all required.
struct zynqmp_uart_regs {
    uint32_t cr;        /* 0x000 Control Register [8:0] */
    uint32_t mr;        /* 0x004 Mode Register [9:0] */
    uint32_t ier;       /* 0x008 Interrupt Enable [12:0] */
    uint32_t idr;       /* 0x00c Interrupt Disable [12:0] */
    uint32_t imr;       /* 0x010 Interrupt Mask [12:0] */
    uint32_t isr;       /* 0x014 Interrupt Status [12:0] */
    uint32_t baudgen;   /* 0x018 Baud Rate Generator [15:0] */
    uint32_t rxtout;    /* 0x01c RX Timeout [7:0] */
    uint32_t rxwm;      /* 0x020 RX FIFO Trigger Level [5:0] */
    uint32_t modemcr;   /* 0x024 Modem Control [5:0] */
    uint32_t modemsr;   /* 0x028 Modem Status [8:0] */
    uint32_t sr;        /* 0x02c Channel Status [14:0] */
    uint32_t fifo;      /* 0x030 FIFO [7:0] */
    uint32_t bauddiv;   /* 0x034 Baud Rate Divider [7:0] */
    uint32_t flowdel;   /* 0x038 Flow Delay [5:0] */
    uint32_t res1;      /* 0x03C Reserved */
    uint32_t res2;      /* 0x040 Reserved */
    uint32_t txwm;      /* 0x044 TX FIFO Trigger Level [5:0] */
    uint32_t rxbs;      /* 0x048 RX FIFO Byte Status [11:0] */
    /* The rest of the registers are either reserved or not used */
};
// This variable will have the address of the UART device. Preset by SDDF.
typedef volatile struct zynqmp_uart_regs zynqmp_uart_regs_t;

#define ZYNQMP_UART_CHANNEL_STS_RXEMPTY (1 << 1)
#define ZYNQMP_UART_CHANNEL_STS_RXFULL (1 << 2)
#define ZYNQMP_UART_CHANNEL_STS_TXFULL (1 << 3)
#define ZYNQMP_UART_CHANNEL_STS_TXEMPTY (1 << 4)
#define ZYNQMP_UART_CHANNEL_STS_TXACTIVE (1 << 11)

#define ZYNQMP_UART_CR_TX_DIS_SHIFT 5
#define ZYNQMP_UART_CR_RX_DIS_SHIFT 3
#define ZYNQMP_UART_CR_TX_EN_SHIFT 4
#define ZYNQMP_UART_CR_RX_EN_SHIFT 2
#define ZYNQMP_UART_CR_TX_EN        (1 << ZYNQMP_UART_CR_TX_EN_SHIFT)
#define ZYNQMP_UART_CR_TX_DIS       (1 << ZYNQMP_UART_CR_TX_DIS_SHIFT)
#define ZYNQMP_UART_CR_TX_RST       (1 << 1)
#define ZYNQMP_UART_CR_RX_EN        (1 << ZYNQMP_UART_CR_RX_EN_SHIFT)
#define ZYNQMP_UART_CR_RX_DIS       (1 << ZYNQMP_UART_CR_RX_DIS_SHIFT)
#define ZYNQMP_UART_CR_RX_RST       (1 << 0)

#define ZYNQMO_UART_MR_CCLK             0x00000400U /**< Input clock selection */
#define ZYNQMO_UART_MR_CHMODE_R_LOOP    0x00000300U /**< Remote loopback mode */
#define ZYNQMO_UART_MR_CHMODE_L_LOOP    0x00000200U /**< Local loopback mode */
#define ZYNQMO_UART_MR_CHMODE_ECHO      0x00000100U /**< Auto echo mode */
#define ZYNQMO_UART_MR_CHMODE_NORM      0x00000000U /**< Normal mode */
#define ZYNQMO_UART_MR_CHMODE_SHIFT             8U  /**< Mode shift */
#define ZYNQMO_UART_MR_CHMODE_MASK      0x00000300U /**< Mode mask */
#define ZYNQMO_UART_MR_STOPMODE_2_BIT   0x00000080U /**< 2 stop bits */
#define ZYNQMO_UART_MR_STOPMODE_1_5_BIT 0x00000040U /**< 1.5 stop bits */
#define ZYNQMO_UART_MR_STOPMODE_1_BIT   0x00000000U /**< 1 stop bit */
#define ZYNQMO_UART_MR_STOPMODE_SHIFT           6U  /**< Stop bits shift */
#define ZYNQMO_UART_MR_STOPMODE_MASK    0x000000A0U /**< Stop bits mask */
#define ZYNQMO_UART_MR_PARITY_NONE      0x00000020U /**< No parity mode */
#define ZYNQMO_UART_MR_PARITY_MARK      0x00000018U /**< Mark parity mode */
#define ZYNQMO_UART_MR_PARITY_SPACE     0x00000010U /**< Space parity mode */
#define ZYNQMO_UART_MR_PARITY_ODD       0x00000008U /**< Odd parity mode */
#define ZYNQMO_UART_MR_PARITY_EVEN      0x00000000U /**< Even parity mode */
#define ZYNQMO_UART_MR_PARITY_SHIFT             3U  /**< Parity setting shift */
#define ZYNQMO_UART_MR_PARITY_MASK      0x00000038U /**< Parity mask */
#define ZYNQMO_UART_MR_CHARLEN_6_BIT    0x00000006U /**< 6 bits data */
#define ZYNQMO_UART_MR_CHARLEN_7_BIT    0x00000004U /**< 7 bits data */
#define ZYNQMO_UART_MR_CHARLEN_8_BIT    0x00000000U /**< 8 bits data */
#define ZYNQMO_UART_MR_CHARLEN_SHIFT            1U  /**< Data Length shift */
#define ZYNQMO_UART_MR_CHARLEN_MASK     0x00000006U /**< Data length mask */
#define ZYNQMO_UART_MR_CLKSEL           0x00000001U /**< Input clock selection */

#define ZYNQMO_UART_IXR_RBRK    0x00002000U /**< Rx FIFO break detect interrupt */
#define ZYNQMO_UART_IXR_TOVR    0x00001000U /**< Tx FIFO Overflow interrupt */
#define ZYNQMO_UART_IXR_TNFUL   0x00000800U /**< Tx FIFO Nearly Full interrupt */
#define ZYNQMO_UART_IXR_TTRIG   0x00000400U /**< Tx Trig interrupt */
#define ZYNQMO_UART_IXR_DMS     0x00000200U /**< Modem status change interrupt */
#define ZYNQMO_UART_IXR_TOUT    0x00000100U /**< Timeout error interrupt */
#define ZYNQMO_UART_IXR_PARITY  0x00000080U /**< Parity error interrupt */
#define ZYNQMO_UART_IXR_FRAMING 0x00000040U /**< Framing error interrupt */
#define ZYNQMO_UART_IXR_OVER    0x00000020U /**< Overrun error interrupt */
#define ZYNQMO_UART_IXR_TXFULL  0x00000010U /**< TX FIFO full interrupt. */
#define ZYNQMO_UART_IXR_TXEMPTY 0x00000008U /**< TX FIFO empty interrupt. */
#define ZYNQMO_UART_IXR_RXFULL  0x00000004U /**< RX FIFO full interrupt. */
#define ZYNQMO_UART_IXR_RXEMPTY 0x00000002U /**< RX FIFO empty interrupt. */
#define ZYNQMO_UART_IXR_RXOVR   0x00000001U /**< RX FIFO trigger interrupt. */
#define ZYNQMO_UART_IXR_MASK    0x00003FFFU /**< Valid bit mask */
