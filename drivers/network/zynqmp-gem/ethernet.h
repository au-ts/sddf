/*
 * Copyright 2026, Skykraft
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* The reference manual used to acquire these values:
 * Zynq UltraScale+ Device Technical Reference Manual
 * Document number: UG1085
 * Rev. 2.5, 21st March 2025
 *
 * The ethernet device is described in Chapter 34
 */

/* Table 34-8: TX Buffer Descriptor Entry
 *
 */
/* TX Descriptor Word 0 bits */
#define TXD_ADDR_MASK   (0xFFFFFFFF)  /* Address bits 31:0 */

/* TX Descriptor Word 1 bits */
#define TXD_USED        (1UL << 31)   /* Ownership: 0=HW, 1=SW */
#define TXD_WRAP        (1UL << 30)   /* Wrap bit */
#define TXD_LAST        (1UL << 15)   /* Last buffer in frame */
#define TXD_LEN_MASK    (0x3FFF)      /* Length mask (bits 13:0) */
#define TXD_MK_HW_OWNR  (0UL << 31)

/* Table 34-5: RX Buffer Descriptor Entry
 *
 */
/* RX Descriptor Word 0 bits */
#define RXD_WRAP        (1UL << 1)    /* Wrap bit */
#define RXD_OWN         1UL           /* Ownership: 0=HW, 1=SW */
#define RXD_ADDR_MASK   (0xFFFFFFFC)  /* Address bits 31:2 */
#define RXD_MK_HW_OWNR  0             /* Set ownership to HW */

/* RX Descriptor Word 1 bits */
#define RXD_LEN_MASK    (0x1FFF)      /* Length mask bits (12:0) */

/* Hardware registers structure */
typedef struct zynqmp_gem_regs {
    uint32_t nwctrl;                    /* 0x0 - Network Control reg */
    uint32_t nwcfg;                     /* 0x4 - Network Config reg */
    uint32_t nwsr;                      /* 0x8 - Network Status reg */
    uint32_t reserved1;
    uint32_t dmacr;                     /* 0x10 - DMA Control reg */
    uint32_t txsr;                      /* 0x14 - TX Status reg */
    uint32_t rxqbase;                   /* 0x18 - RX Queue Base address reg */
    uint32_t txqbase;                   /* 0x1c - TX Queue Base address reg */
    uint32_t rxsr;                      /* 0x20 - RX Status reg */
    uint32_t isr;                       /* 0x24 - Interrupt status reg */
    uint32_t ier;                       /* 0x28 - Interrupt enable reg */
    uint32_t idr;                       /* 0x2c - Interrupt Disable reg */
    uint32_t reserved3;                 /* 0x30 - Current interrupt mask register */
    uint32_t phymntnc;                  /* 0x34 - Phy Maintaince reg */
    uint32_t reserved4[18];
    uint32_t hashl;                     /* 0x80 - Hash Low address reg */
    uint32_t hashh;                     /* 0x84 - Hash High address reg */
#define LADDR_LOW    0
#define LADDR_HIGH   1
    uint32_t laddr[4][LADDR_HIGH + 1];  /* 0x88 - Specific1 addr low/high reg */
    uint32_t match[4];                  /* 0xa8 - Type ID1 Match reg */
    uint32_t reserved6[18];
#define STAT_SIZE    44
    uint32_t stat[STAT_SIZE];           /* 0x100 - Octects transmitted Low reg + stat regs */
    uint32_t reserved9[20];
    uint32_t pcscntrl;                  /* 0x200 - PCS control reg */
    uint32_t pcsstatus;                 /* 0x204 - PCS status reg */
    uint32_t reserved12[35];
    uint32_t dcfg6;                     /* 0x294 - Design config reg6 */
    uint32_t reserved7[106];
    uint32_t transmit_q1_ptr;           /* 0x440 - Transmit priority queue 1 */
    uint32_t reserved8[15];
    uint32_t receive_q1_ptr;            /* 0x480 - Receive priority queue 1 */
    uint32_t reserved10[17];
    uint32_t upper_txqbase;             /* 0x4C8 - Upper tx_q base addr */
    uint32_t reserved11[2];
    uint32_t upper_rxqbase;             /* 0x4D4 - Upper rx_q base addr */
    uint32_t screening_type1_0;         /* 0x500 - Screening_type_1_register_0 */
    uint32_t screening_type1_1;         /* 0x504 - Screening_type_1_register_1 */
    uint32_t screening_type1_2;         /* 0x508 - Screening_type_1_register_2 */
    uint32_t screening_type1_3;         /* 0x50c - Screening_type_1_register_3 */
    uint32_t screening_type2_0;         /* 0x540 - Screening_type_2_register_0 */
    uint32_t screening_type2_1;         /* 0x544 - Screening_type_2_register_1 */
    uint32_t screening_type2_2;         /* 0x548 - Screening_type_2_register_2 */
    uint32_t screening_type2_3;         /* 0x54c - Screening_type_2_register_3 */
    uint32_t int_q1_enable;             /* 0x600 - Interrupts enable*/
    uint32_t int_q1_disable;            /* 0x620 - Interrupts disable*/
    uint32_t int_q1_mask;               /* 0x640 - Interrupts mask */
    uint32_t screening_type2_ethertype_0;/* 0x6e0 - Screening_type_2_ethertype_register_0 */
    uint32_t screening_type2_ethertype_1;/* 0x6e4 - Screening_type_2_ethertype_register_1 */
    uint32_t screening_type2_ethertype_2;/* 0x6e8 - Screening_type_2_ethertype_register_2 */
    uint32_t screening_type2_ethertype_3;/* 0x6ec - Screening_type_2_ethertype_register_3 */
    uint32_t type2_comp_0_wrd_0;        /* 0x700 - type2_compare_0_word_0 */
    uint32_t type2_comp_0_wrd_1;        /* 0x704 - type2_compare_0_word_1 */
    uint32_t type2_comp_1_wrd_0;        /* 0x708 - type2_compare_1_word_0 */
    uint32_t type2_comp_1_wrd_1;        /* 0x70c - type2_compare_1_word_1 */
    uint32_t type2_comp_2_wrd_0;        /* 0x710 - type2_compare_2_word_0 */
    uint32_t type2_comp_2_wrd_1;        /* 0x714 - type2_compare_2_word_1 */
    uint32_t type2_comp_3_wrd_0;        /* 0x718 - type2_compare_3_word_0 */
    uint32_t type2_comp_3_wrd_1;        /* 0x71c - type2_compare_3_word_1 */
} zynqmp_gem_regs_t;

/* nwcntrl: Network control register */
#define ZYNQ_GEM_NWCTRL_CLEARSTAT       BIT(5)
#define ZYNQ_GEM_NWCTRL_TXEN_MASK       0x00000008 /* Enable transmit */
#define ZYNQ_GEM_NWCTRL_RXEN_MASK       0x00000004 /* Enable receive */
#define ZYNQ_GEM_NWCTRL_MDEN_MASK       0x00000010 /* Enable MDIO port */
#define ZYNQ_GEM_NWCTRL_STARTTX_MASK    0x00000200 /* Start tx (tx_go) */

/* nwcfg: Network config register */
#define ZYNQ_GEM_NWCFG_SPEED100         0x00000001 /* 100 Mbps operation */
#define ZYNQ_GEM_NWCFG_SPEED1000        0x00000400 /* 1Gbps operation */
#define ZYNQ_GEM_NWCFG_FDEN             0x00000002 /* Full Duplex mode */
#define ZYNQ_GEM_NWCFG_FSREM            0x00020000 /* FCS removal */
#define ZYNQ_GEM_NWCFG_SGMII_ENBL       0x08000000 /* SGMII Enable */
#define ZYNQ_GEM_NWCFG_PCS_SEL          0x00000800 /* PCS select */
#define ZYNQ_GEM_DBUS_WIDTH             (1 << 21)  /* 64 bit bus */
#define ZYNQ_GEM_NWCFG_CPY_ALL_FRAMES   BIT(4)
#define ZYNQ_GEM_NWCFG_CHSUM_EN         (1 << 24)  /* enable checksum offload on receive */
#define ZYNQ_GEM_NWCFG_IEEE_MDC         (0x7 << 18)

/* dmacr: DMA config register */
#define ZYNQ_GEM_DMACR_RXBUF            0x00180000    /* RX DMA Buffer size 1536 bytes */
#define ZYNQ_GEM_DMACR_TXPBUF_32KB      (1UL << 10)   /* TX packet buffer 32KB */
#define ZYNQ_GEM_DMACR_TXPBUF_TCP       (1UL << 11)   /* TX checksum offload */
#define ZYNQ_GEM_DMACR_RXPBUF_SHIFT     8
#define ZYNQ_GEM_DMACR_RXPBUF_MASK      (0x3 << ZYNQ_GEM_DMACR_RXPBUF_SHIFT)
#define ZYNQ_GEM_DMACR_RXPBUF_32KB      (0x3 << ZYNQ_GEM_DMACR_RXPBUF_SHIFT) /* RX packet buffer 32KB */
#define ZYNQ_GEM_DMACR_BLENGTH_MASK     (0x1F)
#define ZYNQ_GEM_DMACR_BLENGTH_16       (0x10)        /* INCR16 bursts */
#define ZYNQ_GEM_DMA_BUS_WIDTH          BIT(30)       /* 64 bit bus */

/* rxsr/txsr: Receive/Transmit status register */
#define ZYNQ_GEM_RXSR_CLEAR             0x0F
#define ZYNQ_GEM_TXSR_CLEAR             0xFF

/* idr/isr: Interrupt Disable/Status register */
#define ZYNQ_GEM_IDR_CLEAR              0x7FFFEFF

/* Interrupts - based on int_status register */
#define ZYNQ_INT_RXC                    BIT(1)  /* Receive completed */
#define ZYNQ_INT_TXC                    BIT(7)  /* Transmit completed */
#define IRQ_MASK                   (ZYNQ_INT_RXC | ZYNQ_INT_TXC) /* Only rx and tx interrupts */