/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* The reference manual used to acquire these values is:
 *
 * i.MX 8M Mini Applications Processor Reference Manual.
 * Document number: IMX8MMRM.
 * Rev. 3, 11/2020.
 *
 * The ethernet device is described in section 11.5.
 */

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

/* Hardware registers */
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

/* The ENET memory map can be found in Section 11.5.5 */
struct enet_regs {
    /* Configuration */
    uint32_t res0[1];
    uint32_t eir;    /* 004 Interrupt Event Register */
    uint32_t eimr;   /* 008 Interrupt Mask Register */
    uint32_t res1[1];
    uint32_t rdar;   /* 010 Receive Descriptor Active Register */
    uint32_t tdar;   /* 014 Transmit Descriptor Active Register */
    uint32_t res2[3];
    uint32_t ecr;    /* 024 Ethernet Control Register */
    uint32_t res3[6];
    uint32_t mmfr;   /* 040 MII Management Frame Register */
    uint32_t mscr;   /* 044 MII Speed Control Register */
    uint32_t res4[7];
    uint32_t mibc;   /* 064 MIB Control Register */
    uint32_t res5[7];
    uint32_t rcr;    /* 084 Receive Control Register */
    uint32_t res6[15];
    uint32_t tcr;    /* 0C4 Transmit Control Register */
    uint32_t res7[7];
    uint32_t palr;   /* 0E4 Physical Address Lower Register */
    uint32_t paur;   /* 0E8 Physical Address Upper Register */
    uint32_t opd;    /* 0EC Opcode/Pause Duration Register */
    uint32_t txic0;  /* 0xf0 Tx Interrupt Coalescing ring 0 */
    uint32_t txic1;  /* 0xf4 Tx Interrupt Coalescing ring 1 */
    uint32_t txic2;  /* 0xf8 Tx Interrupt Coalescing ring 2 */
    uint32_t res8[1];
    uint32_t rxic0;  /* 0x100 Rx Interrupt Coalescing ring 0 */
    uint32_t rxic1;  /* 0x104 Rx Interrupt Coalescing ring 0 */
    uint32_t rxic2;  /* 0x108 Rx Interrupt Coalescing ring 0 */
    uint32_t res8a[3];
    uint32_t iaur;   /* 118 Descriptor Individual Upper Address Register */
    uint32_t ialr;   /* 11C Descriptor Individual Lower Address Register */
    uint32_t gaur;   /* 120 Descriptor Group Upper Address Register */
    uint32_t galr;   /* 124 Descriptor Group Lower Address Register */
    uint32_t res9[7];
    uint32_t tfwr;   /* 144 Transmit FIFO Watermark Register */
    uint32_t res10[14];
    uint32_t rdsr;   /* 180 Receive Descriptor Ring Start Register */
    uint32_t tdsr;   /* 184 Transmit Buffer Descriptor Ring Start Register */
    uint32_t mrbr;   /* 188 Maximum Receive Buffer Size Register */
    uint32_t res12[1];
    uint32_t rsfl;   /* 190 Receive FIFO Section Full Threshold */
    uint32_t rsem;   /* 194 Receive FIFO Section Empty Threshold */
    uint32_t raem;   /* 198 Receive FIFO Almost Empty Threshold */
    uint32_t rafl;   /* 19C Receive FIFO Almost Full Threshold */
    uint32_t tsem;   /* 1A0 Transmit FIFO Section Empty Threshold */
    uint32_t taem;   /* 1A4 Transmit FIFO Almost Empty Threshold */
    uint32_t tafl;   /* 1A8 Transmit FIFO Almost Full Threshold */
    uint32_t tipg;   /* 1AC Transmit Inter-Packet Gap */
    uint32_t ftrl;   /* 1B0 Frame Truncation Length */
    uint32_t res13[3];
    uint32_t tacc;   /* 1C0 Transmit Accelerator Function Configuration */
    uint32_t racc;   /* 1C4 Receive Accelerator Function Configuration */
    uint32_t res14[14];
    /* 0x200: Statistics counters MIB block RFC 2819 */
    struct mib_regs mib;
    uint32_t res15[64];
    /* 0x400: 1588 adjustable timer (TSM) and 1588 frame control */
    uint32_t atcr;   /* 400 Timer Control Register */
    uint32_t atvr;   /* 404 Timer Value Register */
    uint32_t atoff;  /* 408 Timer Offset Register */
    uint32_t atper;  /* 40C Timer Period Register */
    uint32_t atcor;  /* 410 Timer Correction Register */
    uint32_t atinc;  /* 414 Time-Stamping Clock Period Register */
    uint32_t atstmp; /* 418 Timestamp of Last Transmitted Frame */
    uint32_t res16[121];

    /* 0x600: Capture/compare block */
    uint32_t res17[1];
    uint32_t tgsr;   /* 604 Timer Global Status Register */
    uint32_t tcsr0;  /* 608 Timer Control Status Register */
    uint32_t tccr0;  /* 60C Timer Compare Capture Register */
    uint32_t tcsr1;  /* 610 Timer Control Status Register */
    uint32_t tccr1;  /* 614 Timer Compare Capture Register */
    uint32_t tcsr2;  /* 618 Timer Control Status Register */
    uint32_t tccr2;  /* 61C Timer Compare Capture Register */
    uint32_t tcsr3;  /* 620 Timer Control Status Register */
    uint32_t tccr3;  /* 624 Timer Compare Capture Register */
};

struct descriptor {
    uint16_t len;
    uint16_t stat;
    uint32_t addr;
};

/*
 * Housekeeping for NIC ring buffers.
 * Invariants: 0 <= write < cnt
 *             0 <= read < write
 *             remaining = (read - write) % cnt
 *             descr[read] through desc[write]
 *                   are ready to be or have been used for DMA
 *             descr[write % cnt] through descr[(read - 1) % cnt]
 *                   are unused.
 */
typedef struct {
    unsigned int cnt;
    unsigned int write;
    unsigned int read;
    volatile struct descriptor *descr;
    void **cookies;
} ring_ctx_t;

static inline bool
hw_ring_full(ring_ctx_t *ring)
{
    return !((ring->write - ring->read + 1) % ring->cnt);
}

static inline bool
hw_ring_empty(ring_ctx_t *ring)
{
    return !((ring->write - ring->read ) % ring->cnt);
}
