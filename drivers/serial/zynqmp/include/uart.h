/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/util.h>

#if defined(CONFIG_PLAT_ZYNQMP)
/* 100MHz reference UART clock on the zynqmp platform.
   If in doubt, type `clk dump` into the U-Boot shell, `uart0_ref` is your ref clock.
*/
#define ZYNQMP_UART_REF_CLOCK_RATE (100UL * 1000UL * 1000UL)
#else
#error "unknown UART clock"
#endif

/*
* The various constant definitions for xuart are from Xilinx BSP
* and Linux source code for Zynqmp.
*/

/* Register offsets for the UART. */
#define ZYNQMP_UART_CR            0x00  /* Control Register */
#define ZYNQMP_UART_MR            0x04  /* Mode Register */
#define ZYNQMP_UART_IER           0x08  /* Interrupt Enable */
#define ZYNQMP_UART_IDR           0x0C  /* Interrupt Disable */
#define ZYNQMP_UART_IMR           0x10  /* Interrupt Mask */
#define ZYNQMP_UART_ISR           0x14  /* Interrupt Status */
#define ZYNQMP_UART_BAUDGEN       0x18  /* Baud Rate Generator */
#define ZYNQMP_UART_RXTOUT        0x1C  /* RX Timeout */
#define ZYNQMP_UART_RXWM          0x20  /* RX FIFO Trigger Level */
#define ZYNQMP_UART_MODEMCR       0x24  /* Modem Control */
#define ZYNQMP_UART_MODEMSR       0x28  /* Modem Status */
#define ZYNQMP_UART_SR            0x2C  /* Channel Status */
#define ZYNQMP_UART_FIFO          0x30  /* FIFO */
#define ZYNQMP_UART_BAUDDIV       0x34  /* Baud Rate Divider */
#define ZYNQMP_UART_FLOWDEL       0x38  /* Flow Delay */
#define ZYNQMP_UART_IRRX_PWIDTH   0x3C  /* IR Min Received Pulse Width */
#define ZYNQMP_UART_IRTX_PWIDTH   0x40  /* IR Transmitted pulse Width */
#define ZYNQMP_UART_TXWM          0x44  /* TX FIFO Trigger Level */
#define ZYNQMP_UART_RXBS          0x48  /* RX FIFO byte status register */

/* Range of valid UART clock divisors inclusive */
#define ZYNQMP_UART_CD_MIN   2
#define ZYNQMP_UART_CD_MAX   65535
#define ZYNQMP_UART_BDIV_MIN 4
#define ZYNQMP_UART_BDIV_MAX 255

#define ZYNQMP_UART_CHANNEL_STS_RXEMPTY  BIT(1)
#define ZYNQMP_UART_CHANNEL_STS_RXFULL   BIT(2)
#define ZYNQMP_UART_CHANNEL_STS_TXEMPTY  BIT(3)
#define ZYNQMP_UART_CHANNEL_STS_TXFULL   BIT(4)
#define ZYNQMP_UART_CHANNEL_STS_TXACTIVE BIT(11)
#define ZYNQMP_UART_CHANNEL_STS_TXNFULL  BIT(14)

#define ZYNQMP_UART_CR_TX_DIS_SHIFT  5
#define ZYNQMP_UART_CR_RX_DIS_SHIFT  3
#define ZYNQMP_UART_CR_TX_EN_SHIFT   4
#define ZYNQMP_UART_CR_RX_EN_SHIFT   2
#define ZYNQMP_UART_CR_TX_RST_SHIFT  1
#define ZYNQMP_UART_CR_RX_RST_SHIFT  0
#define ZYNQMP_UART_CR_TX_EN         BIT(ZYNQMP_UART_CR_TX_EN_SHIFT)
#define ZYNQMP_UART_CR_TX_DIS        BIT(ZYNQMP_UART_CR_TX_DIS_SHIFT)
#define ZYNQMP_UART_CR_TX_RST        BIT(ZYNQMP_UART_CR_TX_RST_SHIFT)
#define ZYNQMP_UART_CR_RX_EN         BIT(ZYNQMP_UART_CR_RX_EN_SHIFT)
#define ZYNQMP_UART_CR_RX_DIS        BIT(ZYNQMP_UART_CR_RX_DIS_SHIFT)
#define ZYNQMP_UART_CR_RX_RST        BIT(ZYNQMP_UART_CR_RX_RST_SHIFT)

#define ZYNQMP_UART_MR_CCLK             0x00000400U /**< Input clock selection */
#define ZYNQMP_UART_MR_CHMODE_R_LOOP    0x00000300U /**< Remote loopback mode */
#define ZYNQMP_UART_MR_CHMODE_L_LOOP    0x00000200U /**< Local loopback mode */
#define ZYNQMP_UART_MR_CHMODE_ECHO      0x00000100U /**< Auto echo mode */
#define ZYNQMP_UART_MR_CHMODE_NORM      0x00000000U /**< Normal mode */
#define ZYNQMP_UART_MR_CHMODE_SHIFT             8U  /**< Mode shift */
#define ZYNQMP_UART_MR_CHMODE_MASK      0x00000300U /**< Mode mask */
#define ZYNQMP_UART_MR_STOPMODE_2_BIT   0x00000080U /**< 2 stop bits */
#define ZYNQMP_UART_MR_STOPMODE_1_5_BIT 0x00000040U /**< 1.5 stop bits */
#define ZYNQMP_UART_MR_STOPMODE_1_BIT   0x00000000U /**< 1 stop bit */
#define ZYNQMP_UART_MR_STOPMODE_SHIFT           6U  /**< Stop bits shift */
#define ZYNQMP_UART_MR_STOPMODE_MASK    0x000000A0U /**< Stop bits mask */
#define ZYNQMP_UART_MR_PARITY_NONE      0x00000020U /**< No parity mode */
#define ZYNQMP_UART_MR_PARITY_MARK      0x00000018U /**< Mark parity mode */
#define ZYNQMP_UART_MR_PARITY_SPACE     0x00000010U /**< Space parity mode */
#define ZYNQMP_UART_MR_PARITY_ODD       0x00000008U /**< Odd parity mode */
#define ZYNQMP_UART_MR_PARITY_EVEN      0x00000000U /**< Even parity mode */
#define ZYNQMP_UART_MR_PARITY_SHIFT             3U  /**< Parity setting shift */
#define ZYNQMP_UART_MR_PARITY_MASK      0x00000038U /**< Parity mask */
#define ZYNQMP_UART_MR_CHARLEN_6_BIT    0x00000006U /**< 6 bits data */
#define ZYNQMP_UART_MR_CHARLEN_7_BIT    0x00000004U /**< 7 bits data */
#define ZYNQMP_UART_MR_CHARLEN_8_BIT    0x00000000U /**< 8 bits data */
#define ZYNQMP_UART_MR_CHARLEN_SHIFT            1U  /**< Data Length shift */
#define ZYNQMP_UART_MR_CHARLEN_MASK     0x00000006U /**< Data length mask */
#define ZYNQMP_UART_MR_CLKSEL           0x00000001U /**< Input clock selection */

#define ZYNQMP_UART_IXR_RBRK    0x00002000U /**< Rx FIFO break detect interrupt */
#define ZYNQMP_UART_IXR_TOVR    0x00001000U /**< Tx FIFO Overflow interrupt */
#define ZYNQMP_UART_IXR_TNFUL   0x00000800U /**< Tx FIFO Nearly Full interrupt */
#define ZYNQMP_UART_IXR_TTRIG   0x00000400U /**< Tx Trig interrupt */
#define ZYNQMP_UART_IXR_DMS     0x00000200U /**< Modem status change interrupt */
#define ZYNQMP_UART_IXR_TOUT    0x00000100U /**< Timeout error interrupt */
#define ZYNQMP_UART_IXR_PARITY  0x00000080U /**< Parity error interrupt */
#define ZYNQMP_UART_IXR_FRAMING 0x00000040U /**< Framing error interrupt */
#define ZYNQMP_UART_IXR_OVER    0x00000020U /**< Overrun error interrupt */
#define ZYNQMP_UART_IXR_TXFULL  0x00000010U /**< TX FIFO full interrupt. */
#define ZYNQMP_UART_IXR_TXEMPTY 0x00000008U /**< TX FIFO empty interrupt. */
#define ZYNQMP_UART_IXR_RXFULL  0x00000004U /**< RX FIFO full interrupt. */
#define ZYNQMP_UART_IXR_RXEMPTY 0x00000002U /**< RX FIFO empty interrupt. */
#define ZYNQMP_UART_IXR_RXOVR   0x00000001U /**< RX FIFO trigger interrupt. */
#define ZYNQMP_UART_IXR_MASK    0x00001FFFU /**< Valid bit mask */
