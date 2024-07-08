/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

#define DMA_REG_OFFSET              (0x1000)            /* Offset of the DMA Registers. */
#define MAX_RX_FRAME_SZ             (0x600)             /* Maximum size of a received packet. */
#define DMA_PBL                     (32)                /* DMA programmable burst length. Must be 1, 2, 4, 8, 16, or 32. */

/* DMA Bus mode register definitions */
#define DMAMAC_SWRST                (1 << 0)            /* Resets all GMAC Subsystem internal registers and logic. Cleared automatically after the reset operation has completed. */
#define RXHIGHPRIO                  (1 << 1)            /* DMA Arbitration Scheme - 1: Rx has priority over Tx, 0: round robin with Rx:Tx priority given in bits [15:14]. */
#define DSL_MASK                    (0x1c)              /* Number of Words to skip between two unchained descriptors. If 0, descriptor table is taken as contiguous in Ring mode. */
#define DSL_SHFT                    (2)
#define TX_PBL_MASK                 (0x3f00)            /* Maximum number of beats to be transferred in one DMA transaction. */
#define TX_PBL_SHFT                 (8)
#define PRIORXTX_41                 (3 << 14)           /* Rx:Tx priority ratio. RxDMA requests given priority over TxDMA requests in the ratio 4:1. */
#define PRIORXTX_31                 (2 << 14)           /* Rx:Tx priority ratio. RxDMA requests given priority over TxDMA requests in the ratio 3:1. */
#define PRIORXTX_21                 (1 << 14)           /* Rx:Tx priority ratio. RxDMA requests given priority over TxDMA requests in the ratio 2:1. */
#define PRIORXTX_11                 (0 << 14)           /* Rx:Tx priority ratio. RxDMA requests given priority over TxDMA requests in the ratio 1:1. */
#define FIXEDBURST                  (1 << 16)           /* Controls whether the AHB Master interface performs fixed burst transfers or not. */
#define RX_PBL_MASK                 (0x7e0000)          /* Maximum number of beats to be transferred in one RxDMA transaction. Only applicable when USE_SEP_PBL is set. */
#define RX_PBL_SHFT                 (17)
#define USE_SEP_PBL                 (1 << 23)           /* Configures the RxDMA to use the value in bits [22:17] and TxDMA to use value in bits [13:8]. When unset [13:8] is applicable for both DMA engines. */
#define DMA_PBL_X4                  (1 << 24)           /* Multiplies the PBL value programmed (bits[22:17] and bits [13:8]) four times. */

/* DMA Poll demand register definitions - When these bits are written with any value, the DMA reads the current descriptor pointed to by Register 18.
   If that descriptor is not available (owned by Host), transmission returns to the Suspend state and buffer unavailable is asserted in the status register.
   If the descriptor is available, transmission resumes.*/
#define POLL_DATA       0xffffffff

/* DMA status register definitions */
#define DMA_INTR_TXF                (1 << 0)            /* Transmission is finished. */
#define DMA_INTR_TXS                (1 << 1)            /* Transmission is stopped. */
#define DMA_INTR_TXBU               (1 << 2)            /* Next Descriptor in the Transmit List is owned by the host and cannot be acquired by the DMA. Transmission is suspended. */
#define DMA_INTR_TJT                (1 << 3)            /* Transmission Jabber Timeout. */
#define DMA_INTR_ROVF               (1 << 4)            /* Receive Buffer had an Overflow during frame reception. */
#define DMA_INTR_TUNF               (1 << 5)            /* Transmit Buffer had an Underflow during frame transmission. Transmission is suspended. */
#define DMA_INTR_RXF                (1 << 6)            /* Frame has been received. */
#define DMA_INTR_RBU                (1 << 7)            /* Receive Buffer Unavailable. Next Descriptor in the Receive List is owned by the host and cannot be acquired by the DMA. Receive Process is suspended. */
#define DMA_INTR_RXS                (1 << 8)            /* Receive Process Stopped. */
#define DMA_INTR_RWT                (1 << 9)            /* Receive Watchdog Timeout bit is asserted when a frame with a length greater than 2,048 bytes is received. */
#define DMA_INTR_ETI                (1 << 10)           /* Early Transmit Interrupt. */
#define DMA_INTR_FBE                (1 << 13)           /* Fatal Bus Error Interrupt. */
#define DMA_INTR_ERI                (1 << 14)           /* Early Receive Intterupt. DMA had filled the first data buffer of the packet. */
#define DMA_INTR_AIS                (1 << 15)           /* Abnormal Interrupt Summary. Logical OR of interrupts 1, 3, 4, 5, 7, 8, 9, 10, 13. Must be cleared. */
#define DMA_INTR_NIS                (1 << 16)           /* Normal Interrupt Summary. Logical OR of interrupts 0, 2, 6, 14. Must be cleared. */
#define DMA_INTR_RPS_MASK           (0xe0000)           /* Receive DMA process FSM state. */
#define DMA_INTR_TPS_MASK           (0x700000)          /* Transmit DMA process FSM state. */
#define DMA_INTR_ERR_MASK           (0x3800000)         /* Error Bits. Type of error that caused a Bus Error. */

#define DMA_INTR_NORMAL (DMA_INTR_NIS | DMA_INTR_TXF | DMA_INTR_RXF)
#define DMA_INTR_ABNORMAL (DMA_INTR_AIS | DMA_INTR_FBE)
#define DMA_INTR_MASK (DMA_INTR_NORMAL | DMA_INTR_ABNORMAL)

/* DMA operation mode register definitions */
#define RXSTART                     (1 << 1)            /* Place the receive process in the running state. DMA attempts to acquire the descriptor from the Receive list and processes incoming frames. */
#define TX_OPSCND                   (1 << 2)            /* Operate on Second Frame. Instruct the DMA to process a second frame of Transmit data before status for first frame is obtained. */
#define RTC_MASK                    (0x18)              /* Receive Threshold Control. Threshold level of the MTL Receive FIFO. Transfer to DMA starts when the frame size within the MTL Receive FIFO is larger than the threshold. */
#define RTC_SHFT                    (3)
#define RX_FUGF                     (1 << 6)            /* Forward Undersized Good Frames. When set, the Rx FIFO will forward frames with no Error and length less than 64 bytes including pad-bytes and CRC */
#define RX_FEF                      (1 << 7)            /* Forward Error Frames. When this bit is reset, the Rx FIFO drops frames with error status. */
#define EN_FLOWCTL                  (1 << 8)            /* Enable HW flow control. When this bit is set, the flow control signal operation based on fill-level of Rx FIFO is enabled. */
#define FLOWCTL_MASK                (0x600)             /* Threshold for activating flow control. These bits control the Fill level of Rx FIFO at which flow control is activated. */
#define FLOWCTL_SHFT                (9)
#define DISFLOWCTL_MSK              (0x1800)            /* Threshold for deactivating flow control. These bits control the Fill-level of Rx FIFO at which the flow-control is deasserted after activation. */
#define DISFLOWCTL_SHFT             (11)
#define TXSTART                     (1 << 13)            /* Place the transmit process in the Running state. DMA checks the Transmit List at the current position for a frame to be transmitted. */
#define TX_THRSH_MASK               (0x1c000)            /* Transmit Threshold Control. These three bits control the threshold level of the MTL Transmit FIFO. Transmission starts when the frame size within the MTL Transmit FIFO is larger than the threshold*/
#define TX_THRSH_SHFT               (14)
#define FLUSHTXFIFO                 (1 << 20)            /* Flush Transmit FIFO. When this bit is set, the transmit FIFO controller logic is reset to its default values and thus all data in the Tx FIFO is lost/flushed. */
#define STOREFORWARD                (1 << 21)            /* When this bit is set, transmission starts when a full frame resides in the MTL Transmit FIFO. When this bit is set, the TTC values specified in Register6[16:14] are ignored. */
#define DIS_FRMFLUSH                (1 << 24)            /* Disable Flushing of Received Frames. When this bit is set, the RxDMA does not flush any frames due to the unavailability of receive descriptors/buffers as it does normally when this bit is reset. */

/* DMA Missed Frame and Buffer Overflow Counter register definitions */
#define FIFO_OVFLW_BIT              (1 << 28)            /* Overflow bit for FIFO Overflow Counter */
#define FIFO_OVFLW_MSK              (0xffe0000)          /* Indicates missed frames by the application due to buffer overflow conditions. */
#define FIFO_OVFLW_SHFT             (17)
#define MSFRM_OVFLW_BIT             (1 << 16)            /* Overflow bit for Missed Frame Counter */
#define MSFRM_MASK                  (0xffff)             /* Indicates the number of frames missed by the controller due to the Host Receive Buffer being unavailable. */
#define MSFRM_SHFT                  (0)

/* GMAC Configuration register definitions */
#define RX_ENABLE                   (1 << 2)            /* Enables the Receiver state machine of the GMAC for receiving frames. */
#define TX_ENABLE                   (1 << 3)            /* Enables the Transmision state machine of the GMAC for transmitting frames. */
#define IP_CHK_OFFLD                (1 << 10)           /* When this bit is set, the GMAC calculates the checksum of all frame's payloads and checks if the IP header checksum is correct and appends the checksum to the payload. */
#define FULLDPLXMODE                (1 << 11)           /* When this bit is set, the GMAC operates in a Full-Duplex mode where it can transmit and receive simultaneously. */
#define DIS_WTCHDG                  (1 << 23)           /* When this bit is set, the GMAC disables the watchdog timer on the receiver. When this bit is reset, the GMAC allows no more than 2,048 bytes of the receiving frame and cuts off any bytes received after that. */

/* GMAC Frame Filter register definitions */
#define RX_ALL_MODE                 (1 << 31)           /* The GMAC Receiver module passes to the Application all frames received irrespective of whether they pass the address filter. */
#define PMSCUOUS_MODE               (1)                 /* When this bit is set, the Address Filter module passes all incoming frames regardless of its destination or source address. */

/* GMAC Flow Control register definitions */
#define GMAC_FLOW_CTRL_PT_MASK      (0xffff0000)        /* Pause Time Mask */
#define GMAC_FLOW_CTRL_PT_SHIFT     (16)
#define GMAC_FLOW_CTRL_UP           (0x00000008)        /* Unicast pause frame enable */
#define GMAC_FLOW_CTRL_RFE          (0x00000004)        /* Rx Flow Control Enable */
#define GMAC_FLOW_CTRL_TFE          (0x00000002)        /* Tx Flow Control Enable */
#define GMAC_FLOW_CTRL_FCB_BPA      (0x00000001)        /* Flow Control Busy ... */

/* GMAC Interrupt Status Register definitions */
#define GMAC_INT_RGMII              (1)                 /* RGMII Interrupt Status. */
#define GMAC_INT_PCSLNK             (1 << 1)            /* PCS Link Status Changed. */
#define GMAC_INT_PCSAN              (1 << 2)            /* PCS Auto-negotiation Complete. */
#define GMAC_INT_PMT                (1 << 3)            /* PMT Interrupt Status. */
#define GMAC_INT_MMC                (1 << 4)            /* MMC Interrupt Status. */

#define GMAC_INTR_MASK (GMAC_INT_RGMII | GMAC_INT_PCSLNK | GMAC_INT_PCSAN | GMAC_INT_PMT)

/* Descriptor definitions */

/* Rx status bit definitions */
#define DESC_RXSTS_OWNBYDMA         (1 << 31)           /* Descriptor is owned by the DMA of the GMAC Subsystem. */
#define DESC_RXSTS_DAFILTERFAIL     (1 << 30)           /* Frame that failed in the DA Filter in the GMAC Core. */
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
#define DESC_TXCTRL_TXINT           (1 << 31)           /* Sets Transmit Interrupt after the present frame has been transmitted. */
#define DESC_TXCTRL_TXLAST          (1 << 30)           /* Buffer contains the last segment of the frame. */
#define DESC_TXCTRL_TXFIRST         (1 << 29)           /* Buffer contains the first segment of a frame. */
#define DESC_TXCTRL_TXCRCDIS        (1 << 26)           /* GMAC does not append the Cyclic Redundancy Check (CRC) to the end of the transmitted frame.*/
#define DESC_TXCTRL_TXRINGEND       (1 << 25)           /* Descriptor list reached its final descriptor. DMA must loop around. */
#define DESC_TXCTRL_TXCHAIN         (1 << 24)           /* Second address in the descriptor is the Next Descriptor address rather than the second buffer address. */
#define DESC_TXCTRL_SIZE2MASK       (0x3ff800)
#define DESC_TXCTRL_SIZE2SHFT       (11)
#define DESC_TXCTRL_SIZE1MASK       (0x7FF)
#define DESC_TXCTRL_SIZE1SHFT       (0)

struct eth_mac_regs {
    uint32_t conf;                                      /* 0x00 This is the operation mode register for the MAC. */
    uint32_t framefilt;                                 /* 0x04 Contains the frame filtering controls. */
    uint32_t hashtablehigh;                             /* 0x08 Contains the higher 32 bits of the Multicast Hash table. */
    uint32_t hashtablelow;                              /* 0x0c Contains the lower 32 bits of the Multicast Hash table. */
    uint32_t miiaddr;                                   /* 0x10 Controls the management cycles to an external PHY. */
    uint32_t miidata;                                   /* 0x14 Contains the data to be written to or read from the PHY register. */
    uint32_t flowcontrol;                               /* 0x18 Controls the generation of control frames. */
    uint32_t vlantag;                                   /* 0x1c Identifies IEEE 802.1Q VLAN type frames */
    uint32_t version;                                   /* 0x20 Identifies the version of the Core */
    uint32_t debug;                                     /* 0x24 DEBUG register */
    uint32_t wakeup_filter;                             /* 0x28 Wake-up frame filter */
    uint32_t pmt;                                       /* 0x2C PMT control and Status */
    uint32_t reserved_2[2];
    uint32_t intreg;                                    /* 0x38 Contains the interrupt status. */
    uint32_t intmask;                                   /* 0x3c Contains the masks for generating the interrupts. */
    uint32_t macaddr0hi;                                /* 0x40 Contains the higher 16 bits of the first MAC address */
    uint32_t macaddr0lo;                                /* 0x44 Contains the lower 32 bits of the first MAC address. */
};

struct eth_dma_regs {
    uint32_t busmode;                                   /* 0x00 Controls the Host Interface Mode. */
    uint32_t txpolldemand;                              /* 0x04 Used by the host to instruct the DMA to poll the Transmit Descriptor List. */
    uint32_t rxpolldemand;                              /* 0x08 Used by the Host to instruct the DMA to poll the Receive Descriptor list. */
    uint32_t rxdesclistaddr;                            /* 0x0c Points the DMA to the start of the Receive Descriptor list. */
    uint32_t txdesclistaddr;                            /* 0x10 Points the DMA to the start of the Transmit Descriptor List. */
    uint32_t status;                                    /* 0x14 The Software driver (application) reads this register during interrupt service routine or polling to determine the status of the DMA. */
    uint32_t opmode;                                    /* 0x18 Establishes the Receive and Transmit operating modes and command. */
    uint32_t intenable;                                 /* 0x1c Enables the interrupts reported by the Status Register. */
    uint32_t missedframecount;                          /* 0x20 Contains the counters for discarded frames because no host Receive. Descriptor was available, and discarded frames because of Receive FIFO Overflow. */
    uint32_t reserved1[9];
    uint32_t currhosttxdesc;                            /* 0x48 Points to the start of current Transmit Descriptor read by the DMA. */
    uint32_t currhostrxdesc;                            /* 0x4c Points to the start of current Receive Descriptor read by the DMA. */
    uint32_t currhosttxbuffaddr;                        /* 0x50 Points to the current Transmit Buffer address read by the DMA. */
    uint32_t currhostrxbuffaddr;                        /* 0x54 Points to the current Transmit Buffer address read by the DMA. */
};