/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

#define DMA_REG_OFFSET              (0x1000)            /* Offset of the DMA Registers. */
#define MAX_RX_FRAME_SZ             (0x600)             /* Maximum size of a received packet. */
#define DMA_PBL                     (32)                /* DMA programmable burst length. Must be 1, 2, 4, 8, 16, or 32. */

/* THESE REGISTERS DEFINITIONS ARE THE SAME ACROSS DWMAC DEVICES */

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

/* These register definitions are from the dwmac4.h. These are inline with the
register map outlined in the imx8mp TRM. */

/* --------- MAC registers --------- */
#define GMAC_CONFIG			0x00000000
#define GMAC_EXT_CONFIG			0x00000004
#define GMAC_PACKET_FILTER		0x00000008
#define GMAC_HASH_TAB(x)		(0x10 + (x) * 4)
#define GMAC_VLAN_TAG			0x00000050
#define GMAC_VLAN_TAG_DATA		0x00000054
#define GMAC_VLAN_HASH_TABLE		0x00000058
#define GMAC_RX_FLOW_CTRL		0x00000090
#define GMAC_VLAN_INCL			0x00000060
#define GMAC_QX_TX_FLOW_CTRL(x)		(0x70 + x * 4)
#define GMAC_TXQ_PRTY_MAP0		0x98
#define GMAC_TXQ_PRTY_MAP1		0x9C
#define GMAC_RXQ_CTRL0			0x000000a0
#define GMAC_RXQ_CTRL1			0x000000a4
#define GMAC_RXQ_CTRL2			0x000000a8
#define GMAC_RXQ_CTRL3			0x000000ac
#define GMAC_INT_STATUS			0x000000b0
#define GMAC_INT_EN			0x000000b4
#define GMAC_1US_TIC_COUNTER		0x000000dc
#define GMAC_PCS_BASE			0x000000e0
#define GMAC_PHYIF_CONTROL_STATUS	0x000000f8
#define GMAC_PMT			0x000000c0
#define GMAC_DEBUG			0x00000114
#define GMAC_HW_FEATURE0		0x0000011c
#define GMAC_HW_FEATURE1		0x00000120
#define GMAC_HW_FEATURE2		0x00000124
#define GMAC_HW_FEATURE3		0x00000128
#define GMAC_MDIO_ADDR			0x00000200
#define GMAC_MDIO_DATA			0x00000204
#define GMAC_GPIO_STATUS		0x0000020C
#define GMAC_ARP_ADDR			0x00000210
#define GMAC_ADDR_HIGH(reg)		(0x300 + reg * 8)
#define GMAC_ADDR_LOW(reg)		(0x304 + reg * 8)
#define GMAC_L3L4_CTRL(reg)		(0x900 + (reg) * 0x30)
#define GMAC_L4_ADDR(reg)		(0x904 + (reg) * 0x30)
#define GMAC_L3_ADDR0(reg)		(0x910 + (reg) * 0x30)
#define GMAC_L3_ADDR1(reg)		(0x914 + (reg) * 0x30)
#define GMAC_TIMESTAMP_STATUS		0x00000b20

/* RX Queues Routing */
#define GMAC_RXQCTRL_AVCPQ_MASK		GENMASK(2, 0)
#define GMAC_RXQCTRL_AVCPQ_SHIFT	0
#define GMAC_RXQCTRL_PTPQ_MASK		GENMASK(6, 4)
#define GMAC_RXQCTRL_PTPQ_SHIFT		4
#define GMAC_RXQCTRL_DCBCPQ_MASK	GENMASK(10, 8)
#define GMAC_RXQCTRL_DCBCPQ_SHIFT	8
#define GMAC_RXQCTRL_UPQ_MASK		GENMASK(14, 12)
#define GMAC_RXQCTRL_UPQ_SHIFT		12
#define GMAC_RXQCTRL_MCBCQ_MASK		GENMASK(18, 16)
#define GMAC_RXQCTRL_MCBCQ_SHIFT	16
#define GMAC_RXQCTRL_MCBCQEN		BIT(20)
#define GMAC_RXQCTRL_MCBCQEN_SHIFT	20
#define GMAC_RXQCTRL_TACPQE		BIT(21)
#define GMAC_RXQCTRL_TACPQE_SHIFT	21
#define GMAC_RXQCTRL_FPRQ		GENMASK(26, 24)
#define GMAC_RXQCTRL_FPRQ_SHIFT		24

/* MAC Packet Filtering */
#define GMAC_PACKET_FILTER_PR		BIT(0)
#define GMAC_PACKET_FILTER_HMC		BIT(2)
#define GMAC_PACKET_FILTER_PM		BIT(4)
#define GMAC_PACKET_FILTER_PCF		BIT(7)
#define GMAC_PACKET_FILTER_HPF		BIT(10)
#define GMAC_PACKET_FILTER_VTFE		BIT(16)
#define GMAC_PACKET_FILTER_IPFE		BIT(20)
#define GMAC_PACKET_FILTER_RA		BIT(31)

#define GMAC_MAX_PERFECT_ADDRESSES	128

/* MAC VLAN */
#define GMAC_VLAN_EDVLP			BIT(26)
#define GMAC_VLAN_VTHM			BIT(25)
#define GMAC_VLAN_DOVLTC		BIT(20)
#define GMAC_VLAN_ESVL			BIT(18)
#define GMAC_VLAN_ETV			BIT(16)
#define GMAC_VLAN_VID			GENMASK(15, 0)
#define GMAC_VLAN_VLTI			BIT(20)
#define GMAC_VLAN_CSVL			BIT(19)
#define GMAC_VLAN_VLC			GENMASK(17, 16)
#define GMAC_VLAN_VLC_SHIFT		16
#define GMAC_VLAN_VLHT			GENMASK(15, 0)

/* MAC VLAN Tag */
#define GMAC_VLAN_TAG_VID		GENMASK(15, 0)
#define GMAC_VLAN_TAG_ETV		BIT(16)

/* MAC VLAN Tag Control */
#define GMAC_VLAN_TAG_CTRL_OB		BIT(0)
#define GMAC_VLAN_TAG_CTRL_CT		BIT(1)
#define GMAC_VLAN_TAG_CTRL_OFS_MASK	GENMASK(6, 2)
#define GMAC_VLAN_TAG_CTRL_OFS_SHIFT	2
#define GMAC_VLAN_TAG_CTRL_EVLS_MASK	GENMASK(22, 21)
#define GMAC_VLAN_TAG_CTRL_EVLS_SHIFT	21
#define GMAC_VLAN_TAG_CTRL_EVLRXS	BIT(24)

#define GMAC_VLAN_TAG_STRIP_NONE	(0x0 << GMAC_VLAN_TAG_CTRL_EVLS_SHIFT)
#define GMAC_VLAN_TAG_STRIP_PASS	(0x1 << GMAC_VLAN_TAG_CTRL_EVLS_SHIFT)
#define GMAC_VLAN_TAG_STRIP_FAIL	(0x2 << GMAC_VLAN_TAG_CTRL_EVLS_SHIFT)
#define GMAC_VLAN_TAG_STRIP_ALL		(0x3 << GMAC_VLAN_TAG_CTRL_EVLS_SHIFT)

/* MAC VLAN Tag Data/Filter */
#define GMAC_VLAN_TAG_DATA_VID		GENMASK(15, 0)
#define GMAC_VLAN_TAG_DATA_VEN		BIT(16)
#define GMAC_VLAN_TAG_DATA_ETV		BIT(17)

/* MAC RX Queue Enable */
#define GMAC_RX_QUEUE_CLEAR(queue)	~(GENMASK(1, 0) << ((queue) * 2))
#define GMAC_RX_AV_QUEUE_ENABLE(queue)	BIT((queue) * 2)
#define GMAC_RX_DCB_QUEUE_ENABLE(queue)	BIT(((queue) * 2) + 1)

/* MAC Flow Control RX */
#define GMAC_RX_FLOW_CTRL_RFE		BIT(0)

/* RX Queues Priorities */
#define GMAC_RXQCTRL_PSRQX_MASK(x)	GENMASK(7 + ((x) * 8), 0 + ((x) * 8))
#define GMAC_RXQCTRL_PSRQX_SHIFT(x)	((x) * 8)

/* TX Queues Priorities */
#define GMAC_TXQCTRL_PSTQX_MASK(x)	GENMASK(7 + ((x) * 8), 0 + ((x) * 8))
#define GMAC_TXQCTRL_PSTQX_SHIFT(x)	((x) * 8)

/* MAC Flow Control TX */
#define GMAC_TX_FLOW_CTRL_TFE		BIT(1)
#define GMAC_TX_FLOW_CTRL_PT_SHIFT	16

/*  MAC Interrupt bitmap*/
#define GMAC_INT_RGSMIIS		BIT(0)
#define GMAC_INT_PCS_LINK		BIT(1)
#define GMAC_INT_PCS_ANE		BIT(2)
#define GMAC_INT_PCS_PHYIS		BIT(3)
#define GMAC_INT_PMT_EN			BIT(4)
#define GMAC_INT_LPI_EN			BIT(5)
#define GMAC_INT_TSIE			BIT(12)

#define	GMAC_PCS_IRQ_DEFAULT	(GMAC_INT_RGSMIIS | GMAC_INT_PCS_LINK |	\
				 GMAC_INT_PCS_ANE)

#define	GMAC_INT_DEFAULT_ENABLE	(GMAC_INT_PMT_EN | GMAC_INT_LPI_EN | \
				 GMAC_INT_TSIE)

/* MAC Debug bitmap */
#define GMAC_DEBUG_TFCSTS_MASK		GENMASK(18, 17)
#define GMAC_DEBUG_TFCSTS_SHIFT		17
#define GMAC_DEBUG_TFCSTS_IDLE		0
#define GMAC_DEBUG_TFCSTS_WAIT		1
#define GMAC_DEBUG_TFCSTS_GEN_PAUSE	2
#define GMAC_DEBUG_TFCSTS_XFER		3
#define GMAC_DEBUG_TPESTS		BIT(16)
#define GMAC_DEBUG_RFCFCSTS_MASK	GENMASK(2, 1)
#define GMAC_DEBUG_RFCFCSTS_SHIFT	1
#define GMAC_DEBUG_RPESTS		BIT(0)

/* MAC config */
#define GMAC_CONFIG_ARPEN		BIT(31)
#define GMAC_CONFIG_SARC		GENMASK(30, 28)
#define GMAC_CONFIG_SARC_SHIFT		28
#define GMAC_CONFIG_IPC			BIT(27)
#define GMAC_CONFIG_IPG			GENMASK(26, 24)
#define GMAC_CONFIG_IPG_SHIFT		24
#define GMAC_CONFIG_2K			BIT(22)
#define GMAC_CONFIG_ACS			BIT(20)
#define GMAC_CONFIG_BE			BIT(18)
#define GMAC_CONFIG_JD			BIT(17)
#define GMAC_CONFIG_JE			BIT(16)
#define GMAC_CONFIG_PS			BIT(15)
#define GMAC_CONFIG_FES			BIT(14)
#define GMAC_CONFIG_FES_SHIFT		14
#define GMAC_CONFIG_DM			BIT(13)
#define GMAC_CONFIG_LM			BIT(12)
#define GMAC_CONFIG_DCRS		BIT(9)
#define GMAC_CONFIG_TE			BIT(1)
#define GMAC_CONFIG_RE			BIT(0)

/* MAC extended config */
#define GMAC_CONFIG_EIPG		GENMASK(29, 25)
#define GMAC_CONFIG_EIPG_SHIFT		25
#define GMAC_CONFIG_EIPG_EN		BIT(24)
#define GMAC_CONFIG_HDSMS		GENMASK(22, 20)
#define GMAC_CONFIG_HDSMS_SHIFT		20
#define GMAC_CONFIG_HDSMS_256		(0x2 << GMAC_CONFIG_HDSMS_SHIFT)

/* MAC HW features0 bitmap */
#define GMAC_HW_FEAT_SAVLANINS		BIT(27)
#define GMAC_HW_FEAT_ADDMAC		BIT(18)
#define GMAC_HW_FEAT_RXCOESEL		BIT(16)
#define GMAC_HW_FEAT_TXCOSEL		BIT(14)
#define GMAC_HW_FEAT_EEESEL		BIT(13)
#define GMAC_HW_FEAT_TSSEL		BIT(12)
#define GMAC_HW_FEAT_ARPOFFSEL		BIT(9)
#define GMAC_HW_FEAT_MMCSEL		BIT(8)
#define GMAC_HW_FEAT_MGKSEL		BIT(7)
#define GMAC_HW_FEAT_RWKSEL		BIT(6)
#define GMAC_HW_FEAT_SMASEL		BIT(5)
#define GMAC_HW_FEAT_VLHASH		BIT(4)
#define GMAC_HW_FEAT_PCSSEL		BIT(3)
#define GMAC_HW_FEAT_HDSEL		BIT(2)
#define GMAC_HW_FEAT_GMIISEL		BIT(1)
#define GMAC_HW_FEAT_MIISEL		BIT(0)

/* MAC HW features1 bitmap */
#define GMAC_HW_FEAT_L3L4FNUM		GENMASK(30, 27)
#define GMAC_HW_HASH_TB_SZ		GENMASK(25, 24)
#define GMAC_HW_FEAT_AVSEL		BIT(20)
#define GMAC_HW_TSOEN			BIT(18)
#define GMAC_HW_FEAT_SPHEN		BIT(17)
#define GMAC_HW_ADDR64			GENMASK(15, 14)
#define GMAC_HW_TXFIFOSIZE		GENMASK(10, 6)
#define GMAC_HW_RXFIFOSIZE		GENMASK(4, 0)

/* MAC HW features2 bitmap */
#define GMAC_HW_FEAT_AUXSNAPNUM		GENMASK(30, 28)
#define GMAC_HW_FEAT_PPSOUTNUM		GENMASK(26, 24)
#define GMAC_HW_FEAT_TXCHCNT		GENMASK(21, 18)
#define GMAC_HW_FEAT_RXCHCNT		GENMASK(15, 12)
#define GMAC_HW_FEAT_TXQCNT		GENMASK(9, 6)
#define GMAC_HW_FEAT_RXQCNT		GENMASK(3, 0)

/* MAC HW features3 bitmap */
#define GMAC_HW_FEAT_ASP		GENMASK(29, 28)
#define GMAC_HW_FEAT_TBSSEL		BIT(27)
#define GMAC_HW_FEAT_FPESEL		BIT(26)
#define GMAC_HW_FEAT_ESTWID		GENMASK(21, 20)
#define GMAC_HW_FEAT_ESTDEP		GENMASK(19, 17)
#define GMAC_HW_FEAT_ESTSEL		BIT(16)
#define GMAC_HW_FEAT_FRPES		GENMASK(14, 13)
#define GMAC_HW_FEAT_FRPBS		GENMASK(12, 11)
#define GMAC_HW_FEAT_FRPSEL		BIT(10)
#define GMAC_HW_FEAT_DVLAN		BIT(5)
#define GMAC_HW_FEAT_NRVF		GENMASK(2, 0)

/* GMAC GPIO Status reg */
#define GMAC_GPO0			BIT(16)
#define GMAC_GPO1			BIT(17)
#define GMAC_GPO2			BIT(18)
#define GMAC_GPO3			BIT(19)

/* MAC HW ADDR regs */
#define GMAC_HI_DCS			GENMASK(18, 16)
#define GMAC_HI_DCS_SHIFT		16
#define GMAC_HI_REG_AE			BIT(31)

/* L3/L4 Filters regs */
#define GMAC_L4DPIM0			BIT(21)
#define GMAC_L4DPM0			BIT(20)
#define GMAC_L4SPIM0			BIT(19)
#define GMAC_L4SPM0			BIT(18)
#define GMAC_L4PEN0			BIT(16)
#define GMAC_L3DAIM0			BIT(5)
#define GMAC_L3DAM0			BIT(4)
#define GMAC_L3SAIM0			BIT(3)
#define GMAC_L3SAM0			BIT(2)
#define GMAC_L3PEN0			BIT(0)
#define GMAC_L4DP0			GENMASK(31, 16)
#define GMAC_L4DP0_SHIFT		16
#define GMAC_L4SP0			GENMASK(15, 0)

/* MAC Timestamp Status */
#define GMAC_TIMESTAMP_AUXTSTRIG	BIT(2)
#define GMAC_TIMESTAMP_ATSNS_MASK	GENMASK(29, 25)
#define GMAC_TIMESTAMP_ATSNS_SHIFT	25

/* --------- MTL registers --------- */
#define MTL_OPERATION_MODE		0x00000c00
#define MTL_FRPE			BIT(15)
#define MTL_OPERATION_SCHALG_MASK	GENMASK(6, 5)
#define MTL_OPERATION_SCHALG_WRR	(0x0 << 5)
#define MTL_OPERATION_SCHALG_WFQ	(0x1 << 5)
#define MTL_OPERATION_SCHALG_DWRR	(0x2 << 5)
#define MTL_OPERATION_SCHALG_SP		(0x3 << 5)
#define MTL_OPERATION_RAA		BIT(2)
#define MTL_OPERATION_RAA_SP		(0x0 << 2)
#define MTL_OPERATION_RAA_WSP		(0x1 << 2)

#define MTL_INT_STATUS			0x00000c20
#define MTL_INT_QX(x)			BIT(x)

#define MTL_RXQ_DMA_MAP0		0x00000c30 /* queue 0 to 3 */
#define MTL_RXQ_DMA_MAP1		0x00000c34 /* queue 4 to 7 */
#define MTL_RXQ_DMA_QXMDMACH_MASK(x)	(0xf << 8 * (x))
#define MTL_RXQ_DMA_QXMDMACH(chan, q)	((chan) << (8 * (q)))

#define MTL_CHAN_BASE_ADDR		0x00000d00
#define MTL_CHAN_BASE_OFFSET		0x40

#define MTL_CHAN_TX_OP_MODE(x)	MTL_CHAN_BASE_ADDR + (x * MTL_CHAN_BASE_OFFSET);
#define MTL_CHAN_TX_DEBUG(x)	(MTL_CHAN_BASE_ADDR + (x * MTL_CHAN_BASE_OFFSET); + 0x8)
#define MTL_CHAN_INT_CTRL(x)	(MTL_CHAN_BASE_ADDR + (x * MTL_CHAN_BASE_OFFSET); + 0x2c)
#define MTL_CHAN_RX_OP_MODE(x)	(MTL_CHAN_BASE_ADDR + (x * MTL_CHAN_BASE_OFFSET); + 0x30)
#define MTL_CHAN_RX_DEBUG(x)	(MTL_CHAN_BASE_ADDR + (x * MTL_CHAN_BASE_OFFSET); + 0x38)

#define MTL_OP_MODE_RSF			BIT(5)
#define MTL_OP_MODE_TXQEN_MASK		GENMASK(3, 2)
#define MTL_OP_MODE_TXQEN_AV		BIT(2)
#define MTL_OP_MODE_TXQEN		BIT(3)
#define MTL_OP_MODE_TSF			BIT(1)

#define MTL_OP_MODE_TQS_MASK		GENMASK(24, 16)
#define MTL_OP_MODE_TQS_SHIFT		16

#define MTL_OP_MODE_TTC_MASK		0x70
#define MTL_OP_MODE_TTC_SHIFT		4

#define MTL_OP_MODE_TTC_32		0
#define MTL_OP_MODE_TTC_64		(1 << MTL_OP_MODE_TTC_SHIFT)
#define MTL_OP_MODE_TTC_96		(2 << MTL_OP_MODE_TTC_SHIFT)
#define MTL_OP_MODE_TTC_128		(3 << MTL_OP_MODE_TTC_SHIFT)
#define MTL_OP_MODE_TTC_192		(4 << MTL_OP_MODE_TTC_SHIFT)
#define MTL_OP_MODE_TTC_256		(5 << MTL_OP_MODE_TTC_SHIFT)
#define MTL_OP_MODE_TTC_384		(6 << MTL_OP_MODE_TTC_SHIFT)
#define MTL_OP_MODE_TTC_512		(7 << MTL_OP_MODE_TTC_SHIFT)

#define MTL_OP_MODE_RQS_MASK		GENMASK(29, 20)
#define MTL_OP_MODE_RQS_SHIFT		20

#define MTL_OP_MODE_RFD_MASK		GENMASK(19, 14)
#define MTL_OP_MODE_RFD_SHIFT		14

#define MTL_OP_MODE_RFA_MASK		GENMASK(13, 8)
#define MTL_OP_MODE_RFA_SHIFT		8

#define MTL_OP_MODE_EHFC		BIT(7)

#define MTL_OP_MODE_RTC_MASK		0x18
#define MTL_OP_MODE_RTC_SHIFT		3

#define MTL_OP_MODE_RTC_32		(1 << MTL_OP_MODE_RTC_SHIFT)
#define MTL_OP_MODE_RTC_64		0
#define MTL_OP_MODE_RTC_96		(2 << MTL_OP_MODE_RTC_SHIFT)
#define MTL_OP_MODE_RTC_128		(3 << MTL_OP_MODE_RTC_SHIFT)

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