/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
/* The reference manual used to acquire these values:
 * Zynq UltraScale+ Device Technical Reference Manual
 * Document number: UG1085
 * Rev. 2.5, 21st March 2025
 *
 * The ethernet device is described in chapter 34
 */

// TODO: remove below/replace with appropriate gem stuff
#define ECR_RESET       (1UL)
#define ECR_DBSWP       (1UL << 8) /* descriptor byte swapping enable */
#define MIBC_DIS        (1UL << 31)
#define MIBC_IDLE       (1UL << 30)
#define MIBC_CLEAR      (1UL << 29)
#define TIPG            8
#define RACC_LINEDIS    (1UL << 6) /* Discard frames with MAC layer errors */
#define RCR_MII_MODE    (1UL << 2) /* This field must always be set */
#define RCR_RGMII_EN    (1UL << 6) /* RGMII  Mode Enable. RMII must not be set */
#define RCR_PROMISCUOUS (1UL << 3) /* Accept all frames regardless of address matching */
#define ECR_ETHEREN     2
#define ECR_SPEED       (1UL << 5) /* Enable 1000Mbps */
#define PAUSE_OPCODE_FIELD (1UL << 16)
#define TCR_FDEN        (1UL << 2) /* Full duplex enable */
#define ICEN            (1UL << 31) /* enable irq coalescence */

/*
 * Section 11.5.5.1 - Interrupt Event Register (ENET_EIR)
 * Page 3776.
*/
#define NETIRQ_BABR     (1UL << 30) /* Babbling Receive Error          */
#define NETIRQ_BABT     (1UL << 29) /* Babbling Transmit Error         */
#define NETIRQ_GRA      (1UL << 28) /* Graceful Stop Complete          */
#define NETIRQ_TXF      (1UL << 27) /* Transmit Frame Interrupt        */
#define NETIRQ_TXB      (1UL << 26) /* Transmit Buffer Interrupt       */
#define NETIRQ_RXF      (1UL << 25) /* Receive Frame Interrupt         */
#define NETIRQ_RXB      (1UL << 24) /* Receive Buffer Interrupt        */
#define NETIRQ_MII      (1UL << 23) /* MII Interrupt                   */
#define NETIRQ_EBERR    (1UL << 22) /* Ethernet bus error              */
#define NETIRQ_LC       (1UL << 21) /* Late Collision                  */
#define NETIRQ_RL       (1UL << 20) /* Collision Retry Limit           */
#define NETIRQ_UN       (1UL << 19) /* Transmit FIFO Underrun          */
#define NETIRQ_PLR      (1UL << 18) /* Payload Receive Error           */
#define NETIRQ_WAKEUP   (1UL << 17) /* Node Wakeup Request Indication  */
#define NETIRQ_TS_AVAIL (1UL << 16) /* Transmit Timestamp Available    */
#define NETIRQ_TS_TIMER (1UL << 15) /* Timestamp Timer                 */

#define IRQ_MASK        (NETIRQ_RXF | NETIRQ_TXF | NETIRQ_EBERR)

#define RXD_EMPTY       (1UL << 15)
#define WRAP            (1UL << 13)
#define TXD_READY       (1UL << 15)
#define TXD_ADDCRC      (1UL << 10)
#define TXD_LAST        (1UL << 11)


#define RDAR_RDAR       (1UL << 24) /* RX descriptor active */
#define TDAR_TDAR       (1UL << 24) /* TX descriptor active */

#define TACC_IPCHK      (1UL << 3) /* If an IP frame is transmitted, the checksum is inserted automatically */
#define TACC_PROCHK     (1UL << 4)

#define STRFWD          (1UL << 8) /* Store forward must be enabled for checksums. */

#define RACC_IPDIS      (1UL << 1) /* check the IP checksum and discard if wrong. */
#define RACC_PRODIS     (1UL << 2) /* check protocol checksum and discard if wrong. */

#define ICFT(x)       (((x) & 0xff) << 20)
#define RCR_MAX_FL(x) (((x) & 0x3fff) << 16) /* Maximum Frame Length */

/* Hardware registers, sourced from U-boot driver and Technical Reference Manual */
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
    uint32_t reserved2[2];              /* 0x24, 0x28 - interrupt status, non priority queuing, interupt enable */
    uint32_t idr;                       /* 0x2c - Interrupt Disable reg */
    uint32_t reserved3;                 /* 0x30 - Current interrupt mask register */
    uint32_t phymntnc;                  /* 0x34 - Phy Maintaince reg */
    uint32_t reserved4[18];
    uint32_t hashl;                     /* 0x80 - Hash Low address reg */
    uint32_t hashh;                     /* 0x84 - Hash High address reg */
#define LADDR_LOW    0
#define LADDR_HIGH    1
    uint32_t laddr[4][LADDR_HIGH + 1];  /* 0x8c - Specific1 addr low/high reg */
    uint32_t match[4];                  /* 0xa8 - Type ID1 Match reg */
    uint32_t reserved6[18];
#define STAT_SIZE    44
    uint32_t stat[STAT_SIZE];           /* 0x100 - Octects transmitted Low reg + stat regs */
    uint32_t reserved9[20];
    uint32_t pcscntrl;                  /* 0x200 - PCS control reg */
    uint32_t pcsstatus;                 /* 0x204 - PCS status reg */
    uint32_t rserved12[35];
    uint32_t dcfg6;                     /* 0x294 - Design config reg6 */
    uint32_t reserved7[106];
    uint32_t transmit_q1_ptr;           /* 0x440 - Transmit priority queue 1 */
    uint32_t reserved8[15];
    uint32_t receive_q1_ptr;            /* 0x480 - Receive priority queue 1 */
    uint32_t reserved10[17];
    uint32_t upper_txqbase;             /* 0x4C8 - Upper tx_q base addr */
    uint32_t reserved11[2];
    uint32_t upper_rxqbase;             /* 0x4D4 - Upper rx_q base addr */
    /* The rest - unused */
} zynqmp_gem_regs_t;


// TODO: remove below
struct mib_regs {
    /* NOTE: Counter not implemented because it is not applicable (read 0 always).*/
    uint32_t rmon_t_drop;        /* 00 Register Count of frames not counted correctly */
    uint32_t rmon_t_packets;     /* 04 RMON Tx packet count */
    uint32_t rmon_t_bc_pkt;      /* 08 RMON Tx Broadcast Packets */
    uint32_t rmon_t_mc_pkt;      /* 0C RMON Tx Multicast Packets */
    uint32_t rmon_t_crc_align;   /* 10 RMON Tx Packets w CRC/Align error */
    uint32_t rmon_t_undersize;   /* 14 RMON Tx Packets < 64 bytes, good CRC */
    uint32_t rmon_t_oversize;    /* 18 RMON Tx Packets > MAX_FL bytes, good CRC */
    uint32_t rmon_t_frag;        /* 1C RMON Tx Packets < 64 bytes, bad CRC */
    uint32_t rmon_t_jab;         /* 20 RMON Tx Packets > MAX_FL bytes, bad CRC*/
    uint32_t rmon_t_col;         /* 24 RMON Tx collision count */
    uint32_t rmon_t_p64;         /* 28 RMON Tx 64 byte packets */
    uint32_t rmon_t_p65to127n;   /* 2C RMON Tx 65 to 127 byte packets */
    uint32_t rmon_t_p128to255n;  /* 30 RMON Tx 128 to 255 byte packets */
    uint32_t rmon_t_p256to511;   /* 34 RMON Tx 256 to 511 byte packets */
    uint32_t rmon_t_p512to1023;  /* 38 RMON Tx 512 to 1023 byte packets */
    uint32_t rmon_t_p1024to2047; /* 3C RMON Tx 1024 to 2047 byte packets */
    uint32_t rmon_t_p_gte2048;   /* 40 RMON Tx packets w > 2048 bytes */
    uint32_t rmon_t_octets;      /* 44 RMON Tx Octets */
    /* NOTE: Counter not implemented because it is not applicable (read 0 always). */
    uint32_t ieee_t_drop;        /* 48 Count of frames not counted correctly */
    uint32_t ieee_t_frame_ok;    /* 4C Frames Transmitted OK */
    uint32_t ieee_t_1col;        /* 50 Frames Transmitted with Single Collision */
    uint32_t ieee_t_mcol;        /* 54 Frames Transmitted with Multiple Collisions */
    uint32_t ieee_t_def;         /* 58 Frames Transmitted after Deferral Delay */
    uint32_t ieee_t_lcol;        /* 5C Frames Transmitted with Late Collision */
    uint32_t ieee_t_excol;       /* 60 Frames Transmitted with Excessive Collisions */
    uint32_t ieee_t_macerr;      /* 64 Frames Transmitted with Tx FIFO Underrun */
    uint32_t ieee_t_cserr;       /* 68 Frames Transmitted with Carrier Sense Error */
    /* NOTE: Counter not implemented because there is no SQE information available (read 0 always). */
    uint32_t ieee_t_sqe;         /* 6C Frames Transmitted with SQE Error */
    uint32_t ieee_t_fdxfc;       /* 70 Flow Control Pause frames transmitted */
    /* NOTE: Counts total octets (includes header and FCS fields). */
    uint32_t ieee_t_octets_ok;   /* 74 Octet count for Frames Transmitted w/o Error */
    uint32_t res0[3];
    uint32_t rmon_r_packets;     /* 84 RMON Rx packet count */
    uint32_t rmon_r_bc_pkt;      /* 88 RMON Rx Broadcast Packets */
    uint32_t rmon_r_mc_pkt;      /* 8C RMON Rx Multicast Packets */
    uint32_t rmon_r_crc_align;   /* 90 RMON Rx Packets w CRC/Align error */
    uint32_t rmon_r_undersize;   /* 94 RMON Rx Packets < 64 bytes, good CRC */
    uint32_t rmon_r_oversize;    /* 98 RMON Rx Packets > MAX_FL, good CRC */
    uint32_t rmon_r_frag;        /* 9C RMON Rx Packets < 64 bytes, bad CRC */
    uint32_t rmon_r_jab;         /* A0 RMON Rx Packets > MAX_FL bytes, bad CRC  */
    uint32_t rmon_r_resvd_0;     /* A4 Reserved */
    uint32_t rmon_r_p64;         /* A8 RMON Rx 64 byte packets */
    uint32_t rmon_r_p65to127;    /* AC RMON Rx 65 to 127 byte packets */
    uint32_t rmon_r_p128to255;   /* B0 RMON Rx 128 to 255 byte packets */
    uint32_t rmon_r_p256to511;   /* B4 RMON Rx 256 to 511 byte packets */
    uint32_t rmon_r_p512to1023;  /* B8 RMON Rx 512 to 1023 byte packets */
    uint32_t rmon_r_p1024to2047; /* BC RMON Rx 1024 to 2047 byte packets */
    uint32_t rmon_r_p_gte2048;   /* C0 RMON Rx packets w > 2048 bytes */
    uint32_t rmon_r_octets;      /* C4 RMON Rx Octets */
    /* NOTE: Counter increments if a frame with invalid/missing SFD character is
     * detected and has been dropped. None of the other counters increments if
     * this counter increments. */
    uint32_t ieee_r_drop;        /* C8 Count of frames not counted correctly */
    uint32_t ieee_r_frame_ok;    /* CC Frames Received OK */
    uint32_t ieee_r_crc;         /* D0 Frames Received with CRC Error */
    uint32_t ieee_r_align;       /* D4 Frames Received with Alignment Error */
    /* Assume they mean D8... */
    uint32_t ieee_r_macerr;      /* D7 Receive FIFO Overflow count */
    uint32_t ieee_r_fdxfc;       /* DC Flow Control Pause frames received */
    /* NOTE: Counts total octets (includes header and FCS fields ) */
    uint32_t ieee_r_octets_ok;   /* E0 Octet count for Frames Rcvd w/o Error */
    uint32_t res1[7];
};

