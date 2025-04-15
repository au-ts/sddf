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

#define UART_CHANNEL_STS_TXEMPTY 0x8
#define UART_CHANNEL_STS_TXFULL  0x10
#define UART_CHANNEL_STS_RXEMPTY 0x02U // FIXME: Guessed.

#define UART_CHANNEL_STS         0x2C
#define UART_TX_RX_FIFO          0x30

#define UART_CR_TX_EN       (1 << 4)
#define UART_CR_TX_DIS      (1 << 5)
#define UART_CR_RX_EN       (1 << 2)
#define UART_CR_RX_DIS      (1 << 3)

#define XUARTPS_MR_CCLK             0x00000400U /**< Input clock selection */
#define XUARTPS_MR_CHMODE_R_LOOP    0x00000300U /**< Remote loopback mode */
#define XUARTPS_MR_CHMODE_L_LOOP    0x00000200U /**< Local loopback mode */
#define XUARTPS_MR_CHMODE_ECHO      0x00000100U /**< Auto echo mode */
#define XUARTPS_MR_CHMODE_NORM      0x00000000U /**< Normal mode */
#define XUARTPS_MR_CHMODE_SHIFT             8U  /**< Mode shift */
#define XUARTPS_MR_CHMODE_MASK      0x00000300U /**< Mode mask */
#define XUARTPS_MR_STOPMODE_2_BIT   0x00000080U /**< 2 stop bits */
#define XUARTPS_MR_STOPMODE_1_5_BIT 0x00000040U /**< 1.5 stop bits */
#define XUARTPS_MR_STOPMODE_1_BIT   0x00000000U /**< 1 stop bit */
#define XUARTPS_MR_STOPMODE_SHIFT           6U  /**< Stop bits shift */
#define XUARTPS_MR_STOPMODE_MASK    0x000000A0U /**< Stop bits mask */
#define XUARTPS_MR_PARITY_NONE      0x00000020U /**< No parity mode */
#define XUARTPS_MR_PARITY_MARK      0x00000018U /**< Mark parity mode */
#define XUARTPS_MR_PARITY_SPACE     0x00000010U /**< Space parity mode */
#define XUARTPS_MR_PARITY_ODD       0x00000008U /**< Odd parity mode */
#define XUARTPS_MR_PARITY_EVEN      0x00000000U /**< Even parity mode */
#define XUARTPS_MR_PARITY_SHIFT             3U  /**< Parity setting shift */
#define XUARTPS_MR_PARITY_MASK      0x00000038U /**< Parity mask */
#define XUARTPS_MR_CHARLEN_6_BIT    0x00000006U /**< 6 bits data */
#define XUARTPS_MR_CHARLEN_7_BIT    0x00000004U /**< 7 bits data */
#define XUARTPS_MR_CHARLEN_8_BIT    0x00000000U /**< 8 bits data */
#define XUARTPS_MR_CHARLEN_SHIFT            1U  /**< Data Length shift */
#define XUARTPS_MR_CHARLEN_MASK     0x00000006U /**< Data length mask */
#define XUARTPS_MR_CLKSEL           0x00000001U /**< Input clock selection */

#define XUARTPS_IXR_RBRK    0x00002000U /**< Rx FIFO break detect interrupt */
#define XUARTPS_IXR_TOVR    0x00001000U /**< Tx FIFO Overflow interrupt */
#define XUARTPS_IXR_TNFUL   0x00000800U /**< Tx FIFO Nearly Full interrupt */
#define XUARTPS_IXR_TTRIG   0x00000400U /**< Tx Trig interrupt */
#define XUARTPS_IXR_DMS     0x00000200U /**< Modem status change interrupt */
#define XUARTPS_IXR_TOUT    0x00000100U /**< Timeout error interrupt */
#define XUARTPS_IXR_PARITY  0x00000080U /**< Parity error interrupt */
#define XUARTPS_IXR_FRAMING 0x00000040U /**< Framing error interrupt */
#define XUARTPS_IXR_OVER    0x00000020U /**< Overrun error interrupt */
#define XUARTPS_IXR_TXFULL  0x00000010U /**< TX FIFO full interrupt. */
#define XUARTPS_IXR_TXEMPTY 0x00000008U /**< TX FIFO empty interrupt. */
#define XUARTPS_IXR_RXFULL  0x00000004U /**< RX FIFO full interrupt. */
#define XUARTPS_IXR_RXEMPTY 0x00000002U /**< RX FIFO empty interrupt. */
#define XUARTPS_IXR_RXOVR   0x00000001U /**< RX FIFO trigger interrupt. */
#define XUARTPS_IXR_MASK    0x00003FFFU /**< Valid bit mask */

// FIXME: BELOW SHOULD BE UNUSED, ABOVE SHOULD USE ZYNQMP PREFIX.

/* Data Register bits */
#define ZYNQMP_DR_DATA_MASK          0xFF            /* Read or write from/to these bits to rx or tx. */

/* Flag Register bits */
#define ZYNQMP_FR_TXFE               BIT(7)          /* Transmit FIFO empty. */
#define ZYNQMP_FR_RXFF               BIT(6)          /* Receive FIFO full. */
#define ZYNQMP_FR_TXFF               BIT(5)          /* Transmit FIFO full. */
#define ZYNQMP_FR_RXFE               BIT(4)          /* Receive FIFO empty. */
#define ZYNQMP_FR_UART_BUSY          BIT(3)          /* UART busy transmitting data. */

/* Integer Baud Rate Register */
#define ZYNQMP_IBRD_BAUD_INT_MASK    0xFFFF          /* Integer part of baud rate divisor value. */

/* Fractional Baud Rate Register */
#define ZYNQMP_FBRD_BAUD_FRAC_MASK   0x3F            /* Fractional part of baud rate divisor value. */

#define ZYNQMP_UART_REF_CLOCK        0x16E3600

/* Line Control Register bits */
#define ZYNQMP_LCR_WLEN_MASK         0x3             /* Word length. b00 = 5, b01 = 6, b10 = 7, b11 = 8. */
#define ZYNQMP_LCR_WLEN_SHFT         5
#define ZYNQMP_LCR_FIFO_EN           BIT(4)          /* Enable tx and rx FIFOs. */
#define ZYNQMP_LCR_2_STP_BITS        BIT(3)          /* Set this bit to 1 to tx two stop bits. */
#define ZYNQMP_LCR_PARTY_EVEN        BIT(2)          /* Even parity select. */
#define ZYNQMP_LCR_PARTY_EN          BIT(1)          /* Enable parity checks and addition. */

/* Control Register */
#define ZYNQMP_CR_RX_EN              BIT(9)          /* Enable rx. */
#define ZYNQMP_CR_TX_EN              BIT(8)          /* Enable tx. */
#define ZYNQMP_CR_UART_EN            BIT(0)          /* Enable the uart. */

/* Interrupt FIFO Level Select Register */
#define ZYNQMP_IFLS_RX_MASK          0x7             /* Rx interrupt level select. b000 = 1/8, b001 = 1/4, b010 = 1/2, b011 = 3/4, b100 = 7/8. */
#define ZYNQMP_IFLS_RX_SHFT          3
#define ZYNQMP_IFLS_TX_MASK          0x7             /* Tx interrupt level select. b000 = 1/8, b001 = 1/4, b010 = 1/2, b011 = 3/4, b100 = 7/8. */
#define ZYNQMP_IFLS_TX_SHFT          0

/* Interrupt Mask Set/Clear Register */
#define ZYNQMP_IMSC_RX_TIMEOUT       BIT(6)          /* Enable rx timeout interrupt. Occurs when the rx FIFO is not empty, and no more data is received during a 32-bit period. */
#define ZYNQMP_IMSC_TX_INT           BIT(5)          /* Enable tx interrupt when FIFO drops below programmed threshold. */
#define ZYNQMP_IMSC_RX_INT           BIT(4)          /* Enable rx interrupt when FIFO exceeds programmed threshold. */

/* Masked Interrupt Status Register */
#define ZYNQMP_IMSC_RX_TIMEOUT       BIT(6)          /* Rx timeout interrupt. Occurs when the rx FIFO is not empty, and no more data is received during a 32-bit period. */
#define ZYNQMP_IMSC_TX_INT           BIT(5)          /* Tx interrupt when FIFO drops below programmed threshold. */
#define ZYNQMP_IMSC_RX_INT           BIT(4)          /* Rx interrupt when FIFO exceeds programmed threshold. */