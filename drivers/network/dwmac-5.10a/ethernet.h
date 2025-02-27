/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

/* This register description is from the NXP i.MX8MP SoC TRM. */

/* NOTE: This is a subset of the registers available. */

/* Helper macros */

#define BIT(x) (1U << x)
#define MAC_REG(x) ((volatile uint32_t *)(eth_regs + x))
#define MTL_REG(x) ((volatile uint32_t *)(eth_regs + x))
#define DMA_REG(x) ((volatile uint32_t *)(eth_regs + x))
#define MAX_RX_FRAME_SZ             (0x600)

/* MAC Registers */

#define MAC_CONFIGURATION           0x0         /* Establishes the operating mode of the MAC. */
#define MAC_PACKET_FILTER           0x8         /* Contains the filter controls for receiving packets. */
#define MAC_Q0_TX_FLOW_CTRL         0x70        /* Controls the generation and reception of the Control (pause command) packets by the flow control module to the MAC.*/
#define MAC_RX_FLOW_CTRL            0x90        /* Controls the pausing of MAC transmit based on the received Pause packet. */
#define MAC_TXQ_PRTY_MAP0           0x98        /* Contains the priority values assigned to the tx queues. */
#define MAC_RXQ_CTRL0               0xA0        /* Controls the queue management in the MAC receiver. */
#define MAC_INTERRUPT_STATUS        0xB0        /* Contains the status of interrupts. */
#define MAC_INTERRUPT_ENABLE        0xB4        /* Contains the mask for generating the interrupts. */
#define MAC_PHYIF_CONTROL_STATUS    0xF8        /* Indicates the status signals received by the interface from the PHY. */
#define MAC_HW_FEATURE1             0x120       /* Indicates the presence of first set of the optional features of this device. */
#define MAC_ADDRESS0_HIGH           0x300       /* Holds the upper 16 bits of the first 6-byte MAC address. */
#define MAC_ADDRESS0_LOW            0x304       /* Holds the lower 32 bits of the first 6-byte MAC address.*/

/* MAC Configuration Bits */
#define MAC_CONFIG_RE               BIT(0)      /* Receiver enable. 0 = disabled, 1 = enabled. */
#define MAC_CONFIG_TE               BIT(1)      /* Transmitter enable. 0 = disabled, 1 = enabled. */
#define MAC_CONFIG_DM               BIT(13)     /* Duplex mode. 0 = Half-duplex, 1 = Full-duplex. */
#define MAC_CONFIG_FES              BIT(14)     /* This bit, in conjunction with PS selects the speed. */
#define MAC_CONFIG_PS               BIT(15)     /* Port select, selects the ethernet line speed. Used in conjunction with FES. */
#define MAC_CONFIG_JE               BIT(16)     /* Jumbo packet enable, allows packet size of 9018 bytes. 0 = disabled, 1 = enabled. */
#define MAC_CONFIG_JB               BIT(17)     /* Jabber disable. 0 = enabled, 1 = disabled. */
#define MAC_CONFIG_WB               BIT(19)     /* Watchdog disable. 0 = enabled, 1 = disabled. */
#define MAC_CONFIG_ACS              BIT(20)     /* Automatic PAD or CRC stripping. 0 = disabled, 1 = enabled. */
#define MAC_CONFIG_CST              BIT(21)     /* CRC stripping for Type packets. 0 = disabled, 1 = enabled. */
#define MAC_CONFIG_GPSLCE           BIT(23)     /* Giant packet size limit control enable. 0 = disabled, 1 = enabled. */
#define MAC_CONFIG_IPC              BIT(27)     /* Checksum offload. 0 = disabled, 1 = enabled. */

/* MAC Packet Filter Bits */

#define MAC_PACKET_FILTER_PR        BIT(0)      /* Promiscuous mode. */

/* MAC Receive Queue Control 0 Bits */

#define MAC_RXQ_CTRL0_Q0_CLEAR      (BIT(0) | BIT(1))   /* Clear the bits of the RXQ0EN field. */
#define MAC_RXQ_CTRL0_Q0_DCB_GEN_EN BIT(1)      /* Queue enabled for DCB/Generic. */

/* MAC Phy Control Bits */

#define MAC_PHYIF_CONTROL_LINKSTS	BIT(19)		/* Link status, indicates if the link is up (0b1) or down (0b0). */

/* MTL Registers */

#define MTL_OPERATION_MODE          0xC00       /* Establishes the tx and rx operating modes and command. */
#define MTL_RXQ_DMA_MAP0            0xC30       /* Receive Queue and DMA channel mapping 0 register. */
#define MTL_TXQ0_OPERATION_MODE     0xD00       /* Establishes the tx queue 0 operating modes and commands. */
#define MTL_TXQ0_DEBUG              0xD08       /* Gives the debug status of various blocks related to the transmit queue 0. */
#define MTL_Q0_INT_CTRL_STATUS      0xD2C       /* Contains the interrupt enable and status bits for the queue 0 interrupts. */
#define MTL_RXQ0_OPERATION_MODE     0xD30       /* Establishes the receive queue operating modes and command. */
#define MTL_RXQ0_DEBUG              0xD38       /* Gives the debug status of various blocks related ot the receive queue 0. */
#define MTL_RXQ0_CONTROL            0xD3C       /* Controls the receive arbitration and passing of the recv'd packets to the app. */

/* MTL RXQ DMA Map 0 Bits */

#define MTL_RXQ_DMA_MAP0_Q0_MDMACH_MASK  (BIT(0) | BIT(1) | BIT(2)) /* Mask the bits of the Q0MDMACH field (Bits 2 - 0). */
#define MTL_RXQ_DMA_MAP0_Q0_DMA0   ~(MTL_RXQ_DMA_MAP0_Q0_MDMACH_MASK) /* Bits 000 of this field maps MTL queue 0 to DMA channel 0. */

/* MTL TXQ0 Operation Mode Bits */

#define MTL_TXQ_OP_MODE_TSF         BIT(1)      /* Transmit store and forward enable. */
#define MTL_TXQ_OP_MODE_TXQEN       BIT(3)      /* Transmit queue enable. */
#define MTL_TXQ_OP_MODE_TQS_POS     16          /* The position of the TQS field to bit shift with. */
#define MTL_TXQ_OP_MODE_TQS_MASK    (0b11111 << MTL_TXQ_OP_MODE_TQS_POS) /* Mask for the TQS field. */

/* MTL RXQ0 Control Bits */

#define MTL_RXQ_OP_MODE_RSF         BIT(5)      /* Receive queue store and forward mode. */
#define MTL_RXQ_OP_MODE_RQS_POS     20          /* The position of the RQS field to bit shift with. */
#define MTL_RXQ_OP_MODE_RQS_MASK    (0b11111 << MTL_RXQ_OP_MODE_RQS_POS) /* Mask for the RQS field. */

/* DMA Registers */

#define DMA_MODE                    0x1000      /* Establishes the bus operating modes for the DMA. */
#define DMA_CH0_TX_CONTROL          0x1104      /* Controls the Tx features such as PBL, TCP segmentation and Tx channel weights. */
#define DMA_CH0_RX_CONTROL          0x1108      /* Controls the Rx features such as PBL, buffer size and extended status. */
#define DMA_CH0_TXDESC_LIST_ADDR    0x1114      /* Points the DMA to the start of the tx descriptor list. Can only write to this register when tx is stopped. */
#define DMA_CH0_RXDESC_LIST_ADDR    0x111C      /* Points the DMA to the start of the rx descriptor list. Can only write to this register when rx is sopped. */
#define DMA_CH0_TXDESC_TAIL_PTR     0x1120      /* Points to an offset from the base and indicates the location of the last valid tx descriptor. */
#define DMA_CH0_RXDESC_TAIL_PTR     0x1128      /* Points to an offset from the base and indicates the location of the last valid rx descriptor. */
#define DMA_CH0_TXDESC_RING_LENGTH	0x112C		/* Contains the length of the transmit descriptor ring. */
#define DMA_CH0_RXDESC_RING_LENGTH	0x1130		/* Contains the length of the receive descriptor ring. */
#define DMA_CH0_INTERRUPT_EN        0x1134      /* Enables the interrupts that are reported by the DMA_CH0_STATUS register. */
#define DMA_CH0_STATUS              0x1160      /* Software must read this register to get the status during the ISR to determine the status of the DMA device. */

/* DMA Mode Bits */

#define DMA_MODE_SWR                BIT(0)      /* Software reset when this bit is set. */

/* DMA CH0 Tx Control Bits */

#define DMA_CH0_TX_CONTROL_ST       BIT(0)      /* Start or stop transmission. When set, tx is placed in the 'Running' state. */
#define DMA_CH0_TX_CONTROL_OSF      BIT(4)      /* Operate on second packet when this bit is set. */

/* DMA CH0 Rx Control Bits */

#define DMA_CH0_RX_CONTROL_SR       BIT(0)      /* Start or stop receive. When this bit is set DMA attempts to acquire a rx descriptor. */
#define DMA_CH0_RX_RBSZ_POS         1           /* The position of the RBSZ field to use for bit shifting. */
#define DMA_CH0_RX_RBSZ_MASK        (0b11111111111111 << DMA_CH0_RX_RBSZ_POS) /* Mask for the RBSZ field. */

/* DMA CH0 Interrupt Enable Bits */

#define DMA_CH0_INTERRUPT_EN_TIE    BIT(0)      /* Transmit interrupt enable. */
#define DMA_CH0_INTERRUPT_EN_TBUE   BIT(1)      /* Transmit buffer unavailable. Needs to be set with NIE. */
#define DMA_CH0_INTERRUPT_EN_RIE    BIT(6)      /* Receive interrupt enable. */
#define DMA_CH0_INTERRUPT_EN_RBUE   BIT(7)      /* Receive buffer unavailable. Needs to be set with AIE. */
#define DMA_CH0_INTERRUPT_EN_RSE    BIT(8)      /* Receive stopped enable. Needs to be set with AIE. */
#define DMA_CH0_INTERRUPT_EN_RWTE   BIT(9)      /* Receive watchdog timeout enable. Needs to be set with AIE. */
#define DMA_CH0_INTERRUPT_EN_ETIE   BIT(10)     /* Early transmit interrupt enable. Needs to be set with AIE. */
#define DMA_CH0_INTERRUPT_EN_ERIE   BIT(11)     /* Early receive interrupt enable. Needs to be set with NIE. */
#define DMA_CH0_INTERRUPT_EN_FBEE   BIT(12)     /* Fatal bus error enable. Needs to be set with AIE. */
#define DMA_CH0_INTERRUPT_EN_CDEE   BIT(13)     /* Context descriptor error enable. Needs to be set with AIE. */
#define DMA_CH0_INTERRUPT_EN_AIE    BIT(14)     /* Abnormal interrupt summary enable. */
#define DMA_CH0_INTERRUPT_EN_NIE    BIT(15)     /* Normal interrupt summary enable. */

#define DMA_INTR_NORMAL (DMA_CH0_INTERRUPT_EN_TIE | DMA_CH0_INTERRUPT_EN_RIE | DMA_CH0_INTERRUPT_EN_NIE)
#define DMA_INTR_ABNORMAL (DMA_CH0_INTERRUPT_EN_FBEE | DMA_CH0_INTERRUPT_EN_AIE)
#define DMA_INTR_MASK (DMA_INTR_NORMAL | DMA_INTR_ABNORMAL)

/* Rx status bit definitions */
#define DESC_RXSTS_OWNBYDMA         (1 << 31)           /* Descriptor is owned by the DMA of the GMAC Subsystem. */
#define DESC_RXSTS_BUFFER1_ADDR_VALID (1 << 24)			/* Indicates to the DMA that the buffer 1 address specified in RDES1 is valid. */
#define DESC_RXSTS_IOC     			(1 << 30)           /* Interrupt enable on completion. */
#define DESC_RXSTS_LENMSK           (0x3fff0000)        /* Byte length of the received frame that was transferred to Host memory. */
#define DESC_RXSTS_LENSHFT          (16)
#define DESC_RXSTS_ERROR            (1 << 15)           /* Error Summary. */
#define DESC_RXSTS_RXTRUNCATED      (1 << 14)           /* Frame truncation caused by a frame that does not fit within the current descriptor buffers. */
#define DESC_RXSTS_SAFILTERFAIL     (1 << 13)           /* Source Address Filter Fail. */
#define DESC_RXSTS_RXIPC_GIANTFRAME (1 << 12)           /* Length Error. */
#define DESC_RXSTS_RXDAMAGED        (1 << 11)           /* Overflow Error. When set, this bit indicates that the received frame was damaged due to buffer overflow in MTL. */
#define DESC_RXSTS_RXVLANTAG        (1 << 10)           /* Frame pointed to by this descriptor is a VLAN frame tagged by the GMAC Core. */
#define DESC_RXSTS_RXFIRST          (1 << 9)            /* This descriptor contains the first buffer of the frame. */
#define DESC_RXSTS_RXLAST           (1 << 8)            /* The buffers pointed to by this descriptor are the last buffers of the frame. */
#define DESC_RXSTS_RXIPC_GIANT      (1 << 7)            /* IPC Checksum Error/Giant Frame. */
#define DESC_RXSTS_RXCOLLISION      (1 << 6)            /* Late collision has occurred while receiving the frame in Half-duplex mode. */
#define DESC_RXSTS_RXFRAMEETHER     (1 << 5)            /* Indicates that the Receive Frame is an Ethernet-type frame. When this bit is reset, it indicates that the received frame is an IEEE802.3 frame. */
#define DESC_RXSTS_RXWATCHDOG       (1 << 4)            /* The Receive Watchdog Timer has expired while receiving the current frame and the current frame is truncated after the Watchdog Timeout. */
#define DESC_RXSTS_RXMIIERROR       (1 << 3)
#define DESC_RXSTS_RXDRIBBLING      (1 << 2)
#define DESC_RXSTS_RXCRC            (1 << 1)            /* Cyclic Redundancy Check Error. */
#define DESC_RXSTS_RXMAC            (1)                 /* Rx MAC Address registers value matched the DA field of the frame. */

/* Rx control bit definitions */
#define DESC_RXCTRL_RXINTDIS        (1 << 31)           /* Disable Interrupt on Completion. */
#define DESC_RXCTRL_RXRINGEND       (1 << 25)           /* Descriptor list reached its final descriptor. DMA must loop around. */
#define DESC_RXCTRL_RXCHAIN         (1 << 24)           /* Second address in the descriptor is the Next Descriptor address rather than the second buffer address. */
#define DESC_RXCTRL_SIZE2MASK       (0x3ff800)          /* Receive Buffer 2 Size. */
#define DESC_RXCTRL_SIZE2SHFT       (11)
#define DESC_RXCTRL_SIZE1MASK       (0x7FF)             /* Receive Buffer 1 Size. */
#define DESC_RXCTRL_SIZE1SHFT       (0)

/* Tx status bit definitions */
#define DESC_TXSTS_OWNBYDMA         (1 << 31)           /* Descriptor is owned by the DMA of the GMAC Subsystem. */

/* Tx control bit definitions */
#define DESC_TXCTRL_TXINT		    (1 << 31)           /* Sets Transmit Interrupt after the present frame has been transmitted. */
#define DESC_TXCTRL_TXLAST		    (1 << 28)           /* Buffer contains the last segment of the frame. */
#define DESC_TXCTRL_TXFIRST		    (1 << 29)           /* Buffer contains the first segment of a frame. */
#define DESC_TXCTRL_TXCRCDIS		(1 << 26)           /* GMAC does not append the Cyclic Redundancy Check (CRC) to the end of the transmitted frame.*/
#define DESC_TXCTRL_TXRINGEND		(1 << 25)           /* Descriptor list reached its final descriptor. DMA must loop around. */
#define DESC_TXCTRL_TXCHAIN		    (1 << 24)           /* Second address in the descriptor is the Next Descriptor address rather than the second buffer address. */
#define DESC_TXCTRL_TXCIC			(3 << 16)			/* IP header checksum and payload checksum insertion are enabled. Pseudo-header checksum is caclculated in hardware. */
#define DESC_TXCTRL_SIZE2MASK		(0x3ff800)
#define DESC_TXCTRL_SIZE2SHFT		(11)
#define DESC_TXCTRL_SIZE1MASK		(0x7FF)
#define DESC_TXCTRL_SIZE1SHFT		(0)
