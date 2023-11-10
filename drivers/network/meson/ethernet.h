/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

#define DESC_TXSTS_OWNBYDMA     (1 << 31)
#define DESC_TXSTS_MSK          (0x1FFFF << 0)

/* MAC configuration register definitions */
#define FRAMEBURSTENABLE	(1 << 21)
#define MII_PORTSELECT		(1 << 15)
#define FES_100			(1 << 14)
#define DISABLERXOWN		(1 << 13)
#define FULLDPLXMODE		(1 << 11)
#define RXENABLE		(1 << 2)
#define TXENABLE		(1 << 3)

/* rx status bits definitions */
#define DESC_RXSTS_OWNBYDMA     (1 << 31)
#define DESC_RXSTS_DAFILTERFAIL     (1 << 30)
#define DESC_RXSTS_FRMLENMSK        (0x3FFF << 16)
#define DESC_RXSTS_FRMLENSHFT       (16)

#define DESC_RXSTS_ERROR        (1 << 15)
#define DESC_RXSTS_RXTRUNCATED      (1 << 14)
#define DESC_RXSTS_SAFILTERFAIL     (1 << 13)
#define DESC_RXSTS_RXIPC_GIANTFRAME (1 << 12)
#define DESC_RXSTS_RXDAMAGED        (1 << 11)
#define DESC_RXSTS_RXVLANTAG        (1 << 10)
#define DESC_RXSTS_RXFIRST      (1 << 9)
#define DESC_RXSTS_RXLAST       (1 << 8)
#define DESC_RXSTS_RXIPC_GIANT      (1 << 7)
#define DESC_RXSTS_RXCOLLISION      (1 << 6)
#define DESC_RXSTS_RXFRAMEETHER     (1 << 5)
#define DESC_RXSTS_RXWATCHDOG       (1 << 4)
#define DESC_RXSTS_RXMIIERROR       (1 << 3)
#define DESC_RXSTS_RXDRIBBLING      (1 << 2)
#define DESC_RXSTS_RXCRC        (1 << 1)

#define DESC_RXCTRL_RXINTDIS        (1 << 31)
#define DESC_RXCTRL_RXRINGEND       (1 << 25)
#define DESC_RXCTRL_RXCHAIN     (1 << 24)

#define DESC_RXCTRL_SIZE1MASK       (0x7FF << 0)
#define DESC_RXCTRL_SIZE1SHFT       (0)
#define DESC_RXCTRL_SIZE2MASK       (0x7FF << 11)
#define DESC_RXCTRL_SIZE2SHFT       (11)

#define DESC_TXCTRL_TXINT		(1 << 31)
#define DESC_TXCTRL_TXLAST		(1 << 30)
#define DESC_TXCTRL_TXFIRST		(1 << 29)
#define DESC_TXCTRL_TXCHECKINSCTRL	(3 << 27)
#define DESC_TXCTRL_TXCRCDIS		(1 << 26)
#define DESC_TXCTRL_TXRINGEND		(1 << 25)
#define DESC_TXCTRL_TXCHAIN		(1 << 24)

#define DESC_TXCTRL_SIZE1MASK		(0x7FF << 0)
#define DESC_TXCTRL_SIZE1SHFT		(0)
#define DESC_TXCTRL_SIZE2MASK		(0x7FF << 11)
#define DESC_TXCTRL_SIZE2SHFT		(11)

struct eth_mac_regs {
    uint32_t conf;       /* 0x00 */
    uint32_t framefilt;      /* 0x04 */
    uint32_t hashtablehigh;  /* 0x08 */
    uint32_t hashtablelow;   /* 0x0c */
    uint32_t miiaddr;        /* 0x10 */
    uint32_t miidata;        /* 0x14 */
    uint32_t flowcontrol;    /* 0x18 */
    uint32_t vlantag;        /* 0x1c */
    uint32_t version;        /* 0x20 */
    uint32_t reserved_1[5];
    uint32_t intreg;     /* 0x38 */
    uint32_t intmask;        /* 0x3c */
    uint32_t macaddr0hi;     /* 0x40 */
    uint32_t macaddr0lo;     /* 0x44 */
};

struct eth_dma_regs {
    uint32_t busmode;        /* 0x00 */
    uint32_t txpolldemand;   /* 0x04 */
    uint32_t rxpolldemand;   /* 0x08 */
    uint32_t rxdesclistaddr; /* 0x0c */
    uint32_t txdesclistaddr; /* 0x10 */
    uint32_t status;     /* 0x14 */
    uint32_t opmode;     /* 0x18 */
    uint32_t intenable;      /* 0x1c */
    uint32_t reserved1[2];
    uint32_t axibus;     /* 0x28 */
    uint32_t reserved2[7];
    uint32_t currhosttxdesc; /* 0x48 */
    uint32_t currhostrxdesc; /* 0x4c */
    uint32_t currhosttxbuffaddr; /* 0x50 */
    uint32_t currhostrxbuffaddr; /* 0x54 */
};

#define DW_DMA_BASE_OFFSET  (0x1000)

/* Default DMA Burst length */
#define CONFIG_DW_GMAC_DEFAULT_DMA_PBL 8 //1

/* Bus mode register definitions */
#define FIXEDBURST      (1 << 16)
#define PRIORXTX_41     (3 << 14)
#define PRIORXTX_31     (2 << 14)
#define PRIORXTX_21     (1 << 14)
#define PRIORXTX_11     (0 << 14)
#define DMA_PBL         (CONFIG_DW_GMAC_DEFAULT_DMA_PBL<<8)
#define RXHIGHPRIO      (1 << 1)
#define DMAMAC_SRST     (1 << 0)

/* Poll demand definitions */
#define POLL_DATA       0xffffffff

/* Operation mode definitions */
#define STOREFORWARD    (1 << 21)
#define FLUSHTXFIFO     (1 << 20)
#define TXSTART         (1 << 13)
#define TXSECONDFRAME   (1 << 2)
#define RXSTART         (1 << 1)

/* Descriptior related definitions */
#define MAC_MAX_FRAME_SZ    (1536)

#define DMA_INTR_ENA_TIE 0x00000001 /* Transmit interrupt */
#define DMA_INTR_ENA_NIE 0x00010000 /* Normal summary */
#define DMA_INTR_ENA_RIE 0x00000040 /* Receive Interrupt */

#define DMA_INTR_NORMAL (DMA_INTR_ENA_NIE | DMA_INTR_ENA_RIE | \
                    DMA_INTR_ENA_TIE)

#define DMA_INTR_ENA_AIE 0x00008000 /* Abnormal Summary */
#define DMA_INTR_ENA_FBE 0x00002000 /* Fatal Bus Error */
#define DMA_INTR_ENA_UNE 0x00000020 /* Tx Underflow */
#define DMA_INTR_ENA_RBU (1 << 7)   /* receive buffer unavail */
#define DMA_INTR_ENA_RPS (1 << 8)   /* Receive process stopped */
#define DMA_INTR_ENA_RWT (1 << 9)   /* Rx watch dog irq */

#define DMA_INTR_ABNORMAL   (DMA_INTR_ENA_AIE | DMA_INTR_ENA_FBE | \
                        DMA_INTR_ENA_UNE | DMA_INTR_ENA_RBU | DMA_INTR_ENA_RPS)
#define DMA_INTR_DEFAULT_MASK   (DMA_INTR_NORMAL | DMA_INTR_ABNORMAL)

#define        GMAC_INT_MASK           0x0000003c
#define        GMAC_INT_DISABLE_RGMII          0x1
#define        GMAC_INT_DISABLE_PCSLINK        0x2
#define        GMAC_INT_DISABLE_PCSAN          0x4
#define        GMAC_INT_DISABLE_PMT            0x8
#define        GMAC_INT_DISABLE_TIMESTAMP      0x200
#define        GMAC_INT_DISABLE_PCS    (GMAC_INT_DISABLE_RGMII | \
                                GMAC_INT_DISABLE_PCSLINK | \
                                GMAC_INT_DISABLE_PCSAN)
#define        GMAC_INT_DEFAULT_MASK   (GMAC_INT_DISABLE_TIMESTAMP | \
                                GMAC_INT_DISABLE_PCS)
