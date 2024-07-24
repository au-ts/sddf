#pragma once

/* These definitions are taken from the Linux kernel. These are in reference to
the dwmac4 header files. */

#include <stdint.h>

#define BIT(x) (1U << (x))
#define GENMASK(h, l) (((~0UL) << (l)) & (~0UL >> (sizeof(long) * 8 - 1 - (h))))

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

/* DMA status register definitions */
#define DMA_INTR_TI                 (1 << 0)            /* Packet transmission is complete */
#define DMA_INTR_TPS                (1 << 1)            /* Transmit process stopped. */
#define DMA_INTR_TBU                (1 << 2)            /* Next Descriptor in the Transmit List is owned by the host and cannot be acquired by the DMA. Transmission is suspended. */
/* BIT(3) - BIT(5) are reserved. */
#define DMA_INTR_RI                 (1 << 6)            /* Frame has been received. */
#define DMA_INTR_RBU                (1 << 7)            /* Receive Buffer Unavailable. Next Descriptor in the Receive List is owned by the host and cannot be acquired by the DMA. Receive Process is suspended. */
#define DMA_INTR_RPS                (1 << 8)            /* Receive Process Stopped. */
#define DMA_INTR_RWT                (1 << 9)            /* Receive Watchdog Timeout bit is asserted when a frame with a length greater than 2,048 bytes is received. */
#define DMA_INTR_ETI                (1 << 10)           /* Early Transmit Interrupt. */
#define DMA_INTR_ERI                (1 << 11)           /* Early Receive Intterupt. DMA had filled the first data buffer of the packet. */
#define DMA_INTR_FBE                (1 << 12)           /* Fatal Bus Error Interrupt. */
#define DMA_INTR_AIS                (1 << 14)           /* Abnormal Interrupt Summary. Logical OR of interrupts 1, 3, 4, 5, 7, 8, 9, 10, 13. Must be cleared. */
#define DMA_INTR_NIS                (1 << 15)           /* Normal Interrupt Summary. Logical OR of interrupts 0, 2, 6, 14. Must be cleared. */

#define DMA_INTR_RPS_MASK           (0xe0000)           /* Receive DMA process FSM state. */
#define DMA_INTR_TPS_MASK           (0x700000)          /* Transmit DMA process FSM state. */
#define DMA_INTR_ERR_MASK           (0x3800000)         /* Error Bits. Type of error that caused a Bus Error. */

#define DMA_INTR_NORMAL (DMA_INTR_NIS | DMA_INTR_TI | DMA_INTR_RI)
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
#define MTL_OP_MODE_TXQ_ENABLE_MASK		GENMASK(3, 2)
#define MTL_OP_MODE_TXQ_ENABLE_AV		BIT(2)
#define MTL_OP_MODE_TXQ_ENABLE		BIT(3)
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

/* --------- DMA registers --------- */

#define DMA_BUS_MODE			0x00001000
#define DMA_SYS_BUS_MODE		0x00001004
#define DMA_STATUS			0x00001008
#define DMA_DEBUG_STATUS_0		0x0000100c
#define DMA_DEBUG_STATUS_1		0x00001010
#define DMA_DEBUG_STATUS_2		0x00001014
#define DMA_AXI_BUS_MODE		0x00001028
#define DMA_TBS_CTRL			0x00001050

/* DMA Bus Mode bitmap */
#define DMA_BUS_MODE_DCHE		BIT(19)
#define DMA_BUS_MODE_INTM_MASK		GENMASK(17, 16)
#define DMA_BUS_MODE_INTM_SHIFT		16
#define DMA_BUS_MODE_INTM_MODE1		0x1
#define DMA_BUS_MODE_SFT_RESET		BIT(0)

/* DMA SYS Bus Mode bitmap */
#define DMA_BUS_MODE_SPH		BIT(24)
#define DMA_BUS_MODE_PBL		BIT(16)
#define DMA_BUS_MODE_PBL_SHIFT		16
#define DMA_BUS_MODE_RPBL_SHIFT		16
#define DMA_BUS_MODE_MB			BIT(14)
#define DMA_BUS_MODE_FB			BIT(0)

/* DMA Interrupt top status */
#define DMA_STATUS_MAC			BIT(17)
#define DMA_STATUS_MTL			BIT(16)
#define DMA_STATUS_CHAN7		BIT(7)
#define DMA_STATUS_CHAN6		BIT(6)
#define DMA_STATUS_CHAN5		BIT(5)
#define DMA_STATUS_CHAN4		BIT(4)
#define DMA_STATUS_CHAN3		BIT(3)
#define DMA_STATUS_CHAN2		BIT(2)
#define DMA_STATUS_CHAN1		BIT(1)
#define DMA_STATUS_CHAN0		BIT(0)

/* DMA debug status bitmap */
#define DMA_DEBUG_STATUS_TS_MASK	0xf
#define DMA_DEBUG_STATUS_RS_MASK	0xf

/* DMA AXI bitmap */
#define DMA_AXI_EN_LPI			BIT(31)
#define DMA_AXI_LPI_XIT_FRM		BIT(30)
#define DMA_AXI_WR_OSR_LMT		GENMASK(27, 24)
#define DMA_AXI_WR_OSR_LMT_SHIFT	24
#define DMA_AXI_RD_OSR_LMT		GENMASK(19, 16)
#define DMA_AXI_RD_OSR_LMT_SHIFT	16

#define DMA_AXI_OSR_MAX			0xf
#define DMA_AXI_MAX_OSR_LIMIT ((DMA_AXI_OSR_MAX << DMA_AXI_WR_OSR_LMT_SHIFT) | \
				(DMA_AXI_OSR_MAX << DMA_AXI_RD_OSR_LMT_SHIFT))

#define DMA_SYS_BUS_MB			BIT(14)
#define DMA_AXI_1KBBE			BIT(13)
#define DMA_SYS_BUS_AAL			BIT(12)
#define DMA_SYS_BUS_EAME		BIT(11)
#define DMA_AXI_BLEN256			BIT(7)
#define DMA_AXI_BLEN128			BIT(6)
#define DMA_AXI_BLEN64			BIT(5)
#define DMA_AXI_BLEN32			BIT(4)
#define DMA_AXI_BLEN16			BIT(3)
#define DMA_AXI_BLEN8			BIT(2)
#define DMA_AXI_BLEN4			BIT(1)
#define DMA_SYS_BUS_FB			BIT(0)

#define DMA_BURST_LEN_DEFAULT		(DMA_AXI_BLEN256 | DMA_AXI_BLEN128 | \
					DMA_AXI_BLEN64 | DMA_AXI_BLEN32 | \
					DMA_AXI_BLEN16 | DMA_AXI_BLEN8 | \
					DMA_AXI_BLEN4)

#define DMA_AXI_BURST_LEN_MASK		0x000000FE

/* DMA TBS Control */
#define DMA_TBS_FTOS			GENMASK(31, 8)
#define DMA_TBS_FTOV			BIT(0)
#define DMA_TBS_DEF_FTOS		(DMA_TBS_FTOS | DMA_TBS_FTOV)

/* Following DMA defines are channel-oriented */
#define DMA_CHAN_BASE_ADDR		0x00001100
#define DMA_CHAN_BASE_OFFSET		0x80
#define DMA_CHAN_CONTROL(x)             DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET)
#define DMA_CHAN_TX_CONTROL(x)	        (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x4)
#define DMA_CHAN_RX_CONTROL(x)	        (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x8)
#define DMA_CHAN_TX_BASE_ADDR_HI(x)	    (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x10)
#define DMA_CHAN_TX_BASE_ADDR(x)	    (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x14)
#define DMA_CHAN_RX_BASE_ADDR_HI(x)	    (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x18)
#define DMA_CHAN_RX_BASE_ADDR(x)	    (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x1c)
#define DMA_CHAN_TX_TAIL_ADDR(x)	    (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x20)
#define DMA_CHAN_RX_TAIL_ADDR(x)	    (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x28)
#define DMA_CHAN_TX_RING_LEN(x)	        (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x2c)
#define DMA_CHAN_RX_RING_LEN(x)	        (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x30)
#define DMA_CHAN_INTR_ENA(x)	        (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x34)
#define DMA_CHAN_RX_WATCHDOG(x)	        (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x38)
#define DMA_CHAN_SLOT_CTRL_STATUS(x)	(DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x3c)
#define DMA_CHAN_CUR_TX_DESC(x)	        (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x44)
#define DMA_CHAN_CUR_RX_DESC(x)	        (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x4c)
#define DMA_CHAN_CUR_TX_BUF_ADDR(x)	    (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x54)
#define DMA_CHAN_CUR_RX_BUF_ADDR(x)	    (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x5c)
#define DMA_CHAN_STATUS(x)	            (DMA_CHAN_BASE_ADDR + (x * DMA_CHAN_BASE_OFFSET) + 0x60)

/* DMA Control X */
#define DMA_CONTROL_SPH			BIT(24)
#define DMA_CONTROL_MSS_MASK		GENMASK(13, 0)

/* DMA Tx Channel X Control register defines */
#define DMA_CONTROL_EDSE		BIT(28)
#define DMA_CONTROL_TSE			BIT(12)
#define DMA_CONTROL_OSP			BIT(4)
#define DMA_CONTROL_ST			BIT(0)

/* DMA Rx Channel X Control register defines */
#define DMA_CONTROL_SR			BIT(0)
#define DMA_RBSZ_MASK			GENMASK(14, 1)
#define DMA_RBSZ_SHIFT			1

/* Interrupt enable bits per channel */
#define DMA_CHAN_INTR_ENA_NIE		BIT(16)
#define DMA_CHAN_INTR_ENA_AIE		BIT(15)
#define DMA_CHAN_INTR_ENA_NIE_4_10	BIT(15)
#define DMA_CHAN_INTR_ENA_AIE_4_10	BIT(14)
#define DMA_CHAN_INTR_ENA_CDE		BIT(13)
#define DMA_CHAN_INTR_ENA_FBE		BIT(12)
#define DMA_CHAN_INTR_ENA_ERE		BIT(11)
#define DMA_CHAN_INTR_ENA_ETE		BIT(10)
#define DMA_CHAN_INTR_ENA_RWE		BIT(9)
#define DMA_CHAN_INTR_ENA_RSE		BIT(8)
#define DMA_CHAN_INTR_ENA_RBUE		BIT(7)
#define DMA_CHAN_INTR_ENA_RIE		BIT(6)
#define DMA_CHAN_INTR_ENA_TBUE		BIT(2)
#define DMA_CHAN_INTR_ENA_TSE		BIT(1)
#define DMA_CHAN_INTR_ENA_TIE		BIT(0)

#define DMA_CHAN_INTR_NORMAL		(DMA_CHAN_INTR_ENA_NIE_4_10 | \
					 DMA_CHAN_INTR_ENA_RIE | \
					 DMA_CHAN_INTR_ENA_TIE)

#define DMA_CHAN_INTR_ABNORMAL	(DMA_CHAN_INTR_ENA_AIE_4_10 | \
					 DMA_CHAN_INTR_ENA_FBE)

#define DMA_CHAN_INTR_DEFAULT_MASK	(DMA_CHAN_INTR_NORMAL | \
					 DMA_CHAN_INTR_ABNORMAL)
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
#define DESC_TXCTRL_TXINT		    (1 << 31)           /* Sets Transmit Interrupt after the present frame has been transmitted. */
#define DESC_TXCTRL_TXLAST		    (1 << 30)           /* Buffer contains the last segment of the frame. */
#define DESC_TXCTRL_TXFIRST		    (1 << 29)           /* Buffer contains the first segment of a frame. */
#define DESC_TXCTRL_TXCRCDIS		(1 << 26)           /* GMAC does not append the Cyclic Redundancy Check (CRC) to the end of the transmitted frame.*/
#define DESC_TXCTRL_TXRINGEND		(1 << 25)           /* Descriptor list reached its final descriptor. DMA must loop around. */
#define DESC_TXCTRL_TXCHAIN		    (1 << 24)           /* Second address in the descriptor is the Next Descriptor address rather than the second buffer address. */
#define DESC_TXCTRL_SIZE2MASK		(0x3ff800)
#define DESC_TXCTRL_SIZE2SHFT		(11)
#define DESC_TXCTRL_SIZE1MASK		(0x7FF)
#define DESC_TXCTRL_SIZE1SHFT		(0)

/* SGMII/RGMII status register */
#define GMAC_PHYIF_CTRLSTATUS_TC		BIT(0)
#define GMAC_PHYIF_CTRLSTATUS_LUD		BIT(1)
#define GMAC_PHYIF_CTRLSTATUS_SMIDRXS		BIT(4)
#define GMAC_PHYIF_CTRLSTATUS_LNKMOD		BIT(16)
#define GMAC_PHYIF_CTRLSTATUS_SPEED		GENMASK(18, 17)
#define GMAC_PHYIF_CTRLSTATUS_SPEED_SHIFT	17
#define GMAC_PHYIF_CTRLSTATUS_LNKSTS		BIT(19)
#define GMAC_PHYIF_CTRLSTATUS_JABTO		BIT(20)
#define GMAC_PHYIF_CTRLSTATUS_FALSECARDET	BIT(21)
/* LNKMOD */
#define GMAC_PHYIF_CTRLSTATUS_LNKMOD_MASK	0x1
/* LNKSPEED */
#define GMAC_PHYIF_CTRLSTATUS_SPEED_125		0x2
#define GMAC_PHYIF_CTRLSTATUS_SPEED_25		0x1
#define GMAC_PHYIF_CTRLSTATUS_SPEED_2_5		0x0

#define MAC_REGS_BASE 0x000
struct mac_regs {
	uint32_t configuration;				/* 0x000 */
	uint32_t unused_004[(0x070 - 0x004) / 4];	/* 0x004 */
	uint32_t q0_tx_flow_ctrl;			/* 0x070 */
	uint32_t unused_070[(0x090 - 0x074) / 4];	/* 0x074 */
	uint32_t rx_flow_ctrl;				/* 0x090 */
	uint32_t unused_094;				/* 0x094 */
	uint32_t txq_prty_map0;				/* 0x098 */
	uint32_t unused_09c;				/* 0x09c */
	uint32_t rxq_ctrl0;				/* 0x0a0 */
	uint32_t unused_0a4;				/* 0x0a4 */
	uint32_t rxq_ctrl2;				/* 0x0a8 */
	uint32_t unused_0ac[(0x0dc - 0x0ac) / 4];	/* 0x0ac */
	uint32_t us_tic_counter;			/* 0x0dc */
	uint32_t unused_0e0[(0x11c - 0x0e0) / 4];	/* 0x0e0 */
	uint32_t hw_feature0;				/* 0x11c */
	uint32_t hw_feature1;				/* 0x120 */
	uint32_t hw_feature2;				/* 0x124 */
	uint32_t unused_128[(0x200 - 0x128) / 4];	/* 0x128 */
	uint32_t mdio_address;				/* 0x200 */
	uint32_t mdio_data;				/* 0x204 */
	uint32_t unused_208[(0x300 - 0x208) / 4];	/* 0x208 */
	uint32_t address0_high;				/* 0x300 */
	uint32_t address0_low;				/* 0x304 */
};

#define MTL_REGS_BASE 0xd00
struct mtl_regs {
	uint32_t txq0_operation_mode;			/* 0xd00 */
	uint32_t unused_d04;				/* 0xd04 */
	uint32_t txq0_debug;				/* 0xd08 */
	uint32_t unused_d0c[(0xd18 - 0xd0c) / 4];	/* 0xd0c */
	uint32_t txq0_quantum_weight;			/* 0xd18 */
	uint32_t unused_d1c[(0xd30 - 0xd1c) / 4];	/* 0xd1c */
	uint32_t rxq0_operation_mode;			/* 0xd30 */
	uint32_t unused_d34;				/* 0xd34 */
	uint32_t rxq0_debug;				/* 0xd38 */
};

#define DMA_REGS_BASE 0x1000
struct dma_regs {
	uint32_t mode;					/* 0x1000 */
	uint32_t sysbus_mode;				/* 0x1004 */
	uint32_t unused_1008[(0x1100 - 0x1008) / 4];	/* 0x1008 */
	uint32_t ch0_control;				/* 0x1100 */
	uint32_t ch0_tx_control;			/* 0x1104 */
	uint32_t ch0_rx_control;			/* 0x1108 */
	uint32_t unused_110c;				/* 0x110c */
	uint32_t ch0_txdesc_list_haddress;		/* 0x1110 */
	uint32_t ch0_txdesc_list_address;		/* 0x1114 */
	uint32_t ch0_rxdesc_list_haddress;		/* 0x1118 */
	uint32_t ch0_rxdesc_list_address;		/* 0x111c */
	uint32_t ch0_txdesc_tail_pointer;		/* 0x1120 */
	uint32_t unused_1124;				/* 0x1124 */
	uint32_t ch0_rxdesc_tail_pointer;		/* 0x1128 */
	uint32_t ch0_txdesc_ring_length;		/* 0x112c */
	uint32_t ch0_rxdesc_ring_length;		/* 0x1130 */
};