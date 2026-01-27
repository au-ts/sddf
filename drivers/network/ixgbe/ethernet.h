#pragma once

#include <stdint.h>
#include <sddf/util/printf.h>

#define declare_register(name, offset)             \
    uintptr_t name = (uintptr_t)offset;

#define declare_array_register(name, offset, count, multiplier)    \
    static inline                                                       \
    uintptr_t                                                           \
    name(int index) {                                                   \
        if (index >= count) {                                           \
            sddf_dprintf("array register index out of bounds\n");       \
            return 0;                                                   \
        }                                                               \
        return offset + multiplier * index;                             \
    }                                                                   \

declare_register(CTRL, 0x00000);
declare_register(STATUS, 0x00008);
declare_register(CTRL_EXT, 0x00018);
declare_register(EEC, 0x10010);
declare_register(GPRC, 0x04074);
declare_register(GPTC, 0x04080);
declare_register(GORCL, 0x04088);
declare_register(GORCH, 0x0408C);
declare_register(GOTCL, 0x04090);
declare_register(GOTCH, 0x04094);
declare_register(HLREG0, 0x04240);
declare_register(LINKS, 0x042A4);
declare_register(FCTRL, 0x05080);
declare_register(RXCTRL, 0x03000);
declare_register(RDRXCTL, 0x02F00);
declare_register(DTXMXSZRQ, 0x08100);
declare_register(DMATXCTL, 0x04A80);
declare_register(RTTDCS, 0x04900);
declare_register(EICR, 0x00800);
declare_register(EICS, 0x00808);
declare_register(EIMS, 0x00880);
declare_register(EIMC, 0x00888);
declare_register(EIAC, 0x00810);
declare_register(GPIE, 0x00898);
declare_register(TXDGPC, 0x087A0);
declare_register(TXDGBCL, 0x087A4);
declare_register(TXDGBCH, 0x087A8);
declare_register(FACTPS, 0x10150);
declare_array_register(RDBAL, 0x01000, 64, 0x40);
declare_array_register(RDBAH, 0x01004, 64, 0x40);
declare_array_register(RDLEN, 0x01008, 64, 0x60);
declare_array_register(RDH, 0x01010, 64, 0x40);
declare_array_register(RDT, 0x01018, 64, 0x40);
declare_array_register(SRRCTL, 0x01014, 64, 0x40);
declare_array_register(RXPBSIZE, 0x03C00, 8, 0x4);
declare_array_register(DCA_RXCTRL, 0x0100C, 64, 0x40);
declare_array_register(RXDCTL, 0x01028, 64, 0x40);
declare_array_register(RSCCTL, 0x0102C, 64, 0x40);
declare_array_register(TDBAL, 0x06000, 64, 0x40);
declare_array_register(TDBAH, 0x06004, 64, 0x40);
declare_array_register(TDLEN, 0x06008, 64, 0x40);
declare_array_register(TDH, 0x06010, 64, 0x40);
declare_array_register(TDT, 0x06018, 64, 0x40);
declare_array_register(TXPBSIZE, 0x0CC00, 8, 0x4);
declare_array_register(TXPBTHRESH, 0x04950, 8, 0x4);
declare_array_register(TXDCTL, 0x06028, 64, 0x40);
declare_array_register(IVAR, 0x00900, 64, 0x4);
declare_array_register(EITR, 0x00820, 24, 0x4);
declare_array_register(QPTC, 0x08680, 16, 0x4);
declare_array_register(RAL, 0x0A200, 128, 0x8);
declare_array_register(RAH, 0x0A204, 128, 0x8);
declare_array_register(RSCINT, 0x12000, 128, 0x4);

// Queue Packets Received Count
declare_array_register(QPRC, 0x01030, 16, 0x40);
// Queue Packets Received Drop Count
declare_array_register(QPRDC, 0x01430, 16, 0x40);
// Receive Queue Statistic Mapping Registers
declare_array_register(RQSMR, 0x02300, 32, 0x4);

const uint64_t IXGBE_CTRL_LNK_RST = 0x00000008; /* Link Reset. Resets everything. */
const uint64_t IXGBE_CTRL_RST = 0x04000000; /* Reset (SW) */
const uint64_t IXGBE_CTRL_RST_MASK = IXGBE_CTRL_LNK_RST | IXGBE_CTRL_RST;
const uint64_t IXGBE_CTRL_PCIE_MASTER_DISABLE = 1 << 2;

const uint64_t IXGBE_STATUS_PCIE_MASTER_STATUS = 1 << 19;
const uint64_t IXGBE_CTRL_EXT_DRV_LOAD = 1 << 28;

const uint64_t IXGBE_EEC_ARD = 0x00000200; /* EEPROM Auto Read Done */
const uint64_t IXGBE_RDRXCTL_DMAIDONE = 0x00000008; /* DMA init cycle done */

const uint64_t IXGBE_AUTOC_LMS_SHIFT = 13;
const uint64_t IXGBE_AUTOC_LMS_MASK = 0x7 << IXGBE_AUTOC_LMS_SHIFT;
const uint64_t IXGBE_AUTOC_LMS_10G_SERIAL = 0x3 << IXGBE_AUTOC_LMS_SHIFT;
const uint64_t IXGBE_AUTOC_10G_PMA_PMD_MASK = 0x00000180;
const uint64_t IXGBE_AUTOC_10G_PMA_PMD_SHIFT = 7;
const uint64_t IXGBE_AUTOC_10G_XAUI = 0x0 << IXGBE_AUTOC_10G_PMA_PMD_SHIFT;
const uint64_t IXGBE_AUTOC_AN_RESTART = 0x00001000;

const uint64_t IXGBE_RXCTRL_RXEN = 0x00000001; /* Enable Receiver */

const uint64_t IXGBE_RXPBSIZE_128KB = 0x00020000; /* 128KB Packet Buffer */

const uint64_t IXGBE_HLREG0_RXCRCSTRP = 0x00000002; /* bit  1 */
const uint64_t IXGBE_HLREG0_LPBK = 1 << 15;
const uint64_t IXGBE_RDRXCTL_CRCSTRIP = 0x00000002; /* CRC Strip */

const uint64_t IXGBE_FCTRL_BAM = 0x00000400; /* Broadcast Accept Mode */

const uint64_t IXGBE_CTRL_EXT_NS_DIS = 0x00010000; /* No Snoop disable */

const uint64_t IXGBE_HLREG0_TXCRCEN = 0x00000001; /* bit  0 */
const uint64_t IXGBE_HLREG0_TXPADEN = 0x00000400; /* bit 10 */

const uint64_t IXGBE_TXPBSIZE_40KB = 0x0000A000; /* 40KB Packet Buffer */
const uint64_t IXGBE_RTTDCS_ARBDIS = 0x00000040; /* DCB arbiter disable */

const uint64_t IXGBE_DMATXCTL_TE = 0x1; /* Transmit Enable */

const uint64_t IXGBE_RXDCTL_ENABLE = 0x02000000; /* Ena specific Rx Queue, bit 25 */
const uint64_t IXGBE_TXDCTL_ENABLE = 0x02000000; /* Ena specific Tx Queue, bit 25 */
const uint64_t IXGBE_RSCINT_RSCEN = 0x00000001; /* RSC Enable */
const uint64_t IXGBE_RSCCTL_RSCEN = 0x00000001; /* RSC Enable */
/* RSCCTL bit 3:2 Maximum descriptors per large receive */
const uint64_t IXGBE_RSCCTL_MAXDESC_1 = 0x0;    /* 00b = Maximum Descriptors 1 */
const uint64_t IXGBE_RSCCTL_MAXDESC_4 = 0x4;    /* 01b = Maximum Descriptors 4 */
const uint64_t IXGBE_RSCCTL_MAXDESC_8 = 0x8;    /* 10b = Maximum Descriptors 8 */
const uint64_t IXGBE_RSCCTL_MAXDESC_16 = 0xc;   /* 11b = Maximum Descriptors 16 */
const uint64_t IXGBE_EITR_ITR_INTERVAL = 0x00000008; /* bit 3 */

const uint64_t IXGBE_FCTRL_MPE = 0x00000100; /* Multicast Promiscuous Ena*/
const uint64_t IXGBE_FCTRL_UPE = 0x00000200; /* Unicast Promiscuous Ena */

const uint64_t IXGBE_LINKS_UP = 0x40000000;
const uint64_t IXGBE_LINKS_SPEED_82599 = 0x30000000;
const uint64_t IXGBE_LINKS_SPEED_100_82599 = 0x10000000;
const uint64_t IXGBE_LINKS_SPEED_1G_82599 = 0x20000000;
const uint64_t IXGBE_LINKS_SPEED_10G_82599 = 0x30000000;

const uint32_t IXGBE_IVAR_ALLOC_VAL = 0x80; /* Interrupt Allocation valid */
const uint64_t IXGBE_EICR_RTX_QUEUE = 0x0000FFFF; /* RTx Queue Interrupt */

/* Interrupt clear mask */
const uint64_t IXGBE_IRQ_CLEAR_MASK = 0xFFFFFFFF;

const uint64_t IXGBE_GPIE_MSIX_MODE = 0x00000010; /* MSI-X mode */
const uint64_t IXGBE_GPIE_OCD = 0x00000020; /* Other Clear Disable */
const uint64_t IXGBE_GPIE_EIMEN = 0x00000040; /* Immediate Interrupt Enable */
const uint64_t IXGBE_GPIE_EIAME = 0x40000000;
const uint64_t IXGBE_GPIE_PBA_SUPPORT = 0x80000000;

const uint64_t SRRCTL_BSIZEHEADER_MASK = 0b11111100000000;
const uint64_t IXGBE_SRRCTL_DESCTYPE_MASK = 0x0E000000;
const uint64_t IXGBE_SRRCTL_DESCTYPE_ADV_ONEBUF = 0x02000000;
const uint64_t IXGBE_SRRCTL_DROP_EN = 0x10000000;

const uint32_t IXGBE_RXD_STAT_DD = 0x01; /* Descriptor Done */
const uint32_t IXGBE_RXD_STAT_EOP = 0x02; /* End of Packet */
const uint32_t IXGBE_RXDADV_STAT_DD = IXGBE_RXD_STAT_DD; /* Done */
const uint32_t IXGBE_RXDADV_STAT_EOP = IXGBE_RXD_STAT_EOP; /* End of Packet */

const uint32_t IXGBE_ADVTXD_PAYLEN_SHIFT = 14; /* Adv desc PAYLEN shift */
const uint32_t IXGBE_TXD_CMD_EOP = 0x01000000; /* End of Packet */
const uint32_t IXGBE_ADVTXD_DCMD_EOP = IXGBE_TXD_CMD_EOP; /* End of Packet */
const uint32_t IXGBE_TXD_CMD_RS = 0x08000000; /* Report Status */
const uint32_t IXGBE_ADVTXD_DCMD_RS = IXGBE_TXD_CMD_RS; /* Report Status */
const uint32_t IXGBE_TXD_CMD_IFCS = 0x02000000; /* Insert FCS (Ethernet CRC) */
const uint32_t IXGBE_ADVTXD_DCMD_IFCS = IXGBE_TXD_CMD_IFCS; /* Insert FCS */
const uint32_t IXGBE_TXD_CMD_DEXT = 0x20000000; /* Desc extension (0 = legacy) */
const uint32_t IXGBE_ADVTXD_DTYP_DATA = 0x00300000; /* Adv Data Descriptor */
const uint32_t IXGBE_ADVTXD_DCMD_DEXT = IXGBE_TXD_CMD_DEXT; /* Desc ext 1=Adv */
const uint32_t IXGBE_TXD_STAT_DD = 0x00000001; /* Descriptor Done */
const uint32_t IXGBE_ADVTXD_STAT_DD = IXGBE_TXD_STAT_DD; /* Descriptor Done */

// bit 15:0, Receive/Transmit Queue Interrupts, activated on receive/transmit
// events.The mapping of queue to the RTxQ bits is done by the IVAR registers
const uint64_t IXGBE_EICR_RTXQ_BASE = 1;
// Missed packet interrupt is activated for each received packet that
// overflows the Rx packet buffer (overrun)
const uint64_t IXGBE_EICR_RX_MISS = 1 << 17;

typedef struct {
    uint64_t pkt_addr; // Packet buffer address
    uint64_t hdr_addr; // Header buffer address
} ixgbe_adv_rx_desc_read_t;

/* Receive Descriptor - Advanced */
typedef struct {
    uint16_t pkt_info; // RSS, Pkt type
    uint16_t hdr_info; // Splithdr, hdrlen
} ixgbe_adv_rx_desc_wb_lower_lo_dword_hs_rss_t;

typedef union {
    uint32_t data;
    ixgbe_adv_rx_desc_wb_lower_lo_dword_hs_rss_t hs_rss;
} ixgbe_adv_rx_desc_wb_lower_lo_dword_t;

typedef struct {
    uint16_t ip_id; // IP id
    uint16_t csum; // Packet Checksum
} ixgbe_adv_rx_desc_wb_lower_hi_dword_csum_ip_t;

typedef union {
    uint32_t rss; // RSS Hash
    ixgbe_adv_rx_desc_wb_lower_hi_dword_csum_ip_t csum_ip;
} ixgbe_adv_rx_desc_wb_lower_hi_dword_t;

typedef struct {
    ixgbe_adv_rx_desc_wb_lower_lo_dword_t lo_dword;
    ixgbe_adv_rx_desc_wb_lower_hi_dword_t hi_dword;
} ixgbe_adv_rx_desc_wb_lower_t;

typedef struct {
    uint32_t status_error; // ext status/error
    uint16_t length; // Packet length
    uint16_t vlan; // VLAN tag
} ixgbe_adv_rx_desc_wb_upper_t;

typedef struct {
    ixgbe_adv_rx_desc_wb_lower_t lower;
    ixgbe_adv_rx_desc_wb_upper_t upper;
} ixgbe_adv_rx_desc_wb_t;

typedef union {
    ixgbe_adv_rx_desc_read_t read;
    ixgbe_adv_rx_desc_wb_t wb; // writeback
} ixgbe_adv_rx_desc_t;

/* Transmit Descriptor - Advanced */
typedef struct {
    uint64_t buffer_addr; // Address of descriptor's data buf
    uint32_t cmd_type_len;
    uint32_t olinfo_status;
} ixgbe_adv_tx_desc_read_t;

typedef struct {
    uint64_t rsvd; // Reserved
    uint32_t nxtseq_seed;
    uint32_t status;
} ixgbe_adv_tx_desc_wb_t;

typedef union {
    ixgbe_adv_tx_desc_read_t read;
    ixgbe_adv_tx_desc_wb_t wb;
} ixgbe_adv_tx_desc_t;
