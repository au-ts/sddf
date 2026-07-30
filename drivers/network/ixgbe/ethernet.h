/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Intel Ethernet Controller X550 datasheet:
 *   https://www.intel.com/content/www/us/en/content-details/333369/intel-ethernet-controller-x550-datasheet.html
 */
#pragma once

#include <stdint.h>
#include <sddf/util/printf.h>

#define PCIE_CONFIG_BASE 0x3000000lu
#define DEVICE_BASE 0x2000000lu
#define DEVICE_MSIX_TABLE 0x4000000lu

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


#define IXGBE_TXPBSIZE_MAX 0x00028000 /* 160KB, section 7.2.1.2.2 */

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

typedef struct {
    uint32_t lo;
    uint32_t hi;
} rx_addr_t;

typedef struct {
    uint32_t rdbal;           // 0x00001000 + 0x40*n Receive Descriptor Base Address Low
    uint32_t rdbah;           // 0x00001004 + 0x40*n Receive Descriptor Base Address High
    uint32_t rdlen;           // 0x00001008 + 0x40*n Receive Descriptor Length
    uint8_t unused1[4];       // 0x0000100C + 0x40*n
    uint32_t rdh;             // 0x00001010 + 0x40*n Receive Descriptor Head
    uint32_t srrctl;          // 0x00001014 + 0x40*n Split Receive Control Registers
    uint32_t rdt;             // 0x00001018 + 0x40*n Receive Descriptor Tail
    uint8_t unused2[12];      // 0x0000101C + 0x40*n
    uint32_t rxdctl;          // 0x00001028 + 0x40*n Receive Descriptor Control
    uint32_t rscctl;          // 0x0000102C + 0x40*n RSC Control
    uint8_t unused3[16];     // 0x00001030 + 0x40*n
} rx_dma_regs_t;

typedef struct {
    uint32_t tdbal;           // 0x00006000 + 0x40*n Transmit Descriptor Base Address Low
    uint32_t tdbah;           // 0x00006004 + 0x40*n Transmit Descriptor Base Address High
    uint32_t tdlen;           // 0x00006008 + 0x40*n Transmit Descriptor Length
    uint8_t unused1[4];       // 0x0000600C + 0x40*n
    uint32_t tdh;             // 0x00006010 + 0x40*n Transmit Descriptor Head
    uint8_t unused2[4];       // 0x00006014 + 0x40*n
    uint32_t tdt;             // 0x00006018 + 0x40*n Transmit Descriptor Tail
    uint8_t unused3[12];      // 0x0000601C + 0x40*n
    uint32_t txdctl;          // 0x00006028 + 0x40*n Transmit Descriptor Control
    uint8_t unused4[12];      // 0x0000602C + 0x40*n
    uint32_t tdwbal;          // 0x00006038 + 0x40*n Tx Descriptor Completion Write Back Address Low
    uint32_t tdwbah;          // 0x0000603C + 0x40*n Tx Descriptor Completion Write Back Address High
} tx_dma_regs_t;

typedef struct {
    uint32_t ctrl;            // 0x00000 Device Control Register
    uint8_t unused1[4];       // 0x00004
    uint32_t status;          // 0x00008 Device Status Register
    uint8_t unused2[12];      // 0x0000C
    uint32_t ctrl_ext;        // 0x00018 Extended Device Control Register
    uint8_t unused3[2020];    // 0x0001C

    uint32_t eicr;            // 0x00800 Extended Interrupt Cause Register
    uint8_t unused4[4];       // 0x00804
    uint32_t eics;            // 0x00808 Extended Interrupt Cause Set Register
    uint8_t unused5[4];       // 0x0080C
    uint32_t eiac;            // 0x00810 Extended Interrupt Auto Clear Register
    uint8_t unused6[12];      // 0x00814

    uint32_t eitr[24];        // 0x00820 + 0x4*n Extended Interrupt Throttle Registers
    uint32_t eims;            // 0x00880 Extended Interrupt Mask Set/Read Register
    uint8_t unused7[4];       // 0x00884
    uint32_t eimc;            // 0x00888 Extended Interrupt Mask Clear Register
    uint8_t unused8[12];      // 0x0088C
    uint32_t gpie;            // 0x00898 General Purpose Interrupt Enable
    uint8_t unused9[100];     // 0x0089C

    uint32_t ivar[64];        // 0x00900 + 0x4*n Interrupt Vector Allocation Registers
    uint8_t unused10[1536];   // 0x00A00

    rx_dma_regs_t rx_dma[64]; // 0x01000 Receive DMA Registers
    uint8_t unused11[768];    // 0x02000

    uint32_t rqsmr[32];       // 0x02300 + 0x4*n Receive Queue Statistic Mapping Registers
    uint8_t unused12[2944];   // 0x02380

    uint32_t rdrxctl;         // 0x02F00 Receive DMA Control Register
    uint8_t unused13[252];    // 0x02F04

    uint32_t rxctrl;          // 0x03000 Receive Control Register
    uint8_t unused14[3068];   // 0x03004

    uint32_t rxpbsize[8];     // 0x03C00 + 0x4*n Receive Packet Buffer Size
    uint8_t unused15[1108];   // 0x03C20

    uint32_t gprc;            // 0x04074 Good Packets Received Count
    uint8_t unused16[8];      // 0x04078
    uint32_t gptc;            // 0x04080 Good Packets Transmitted Count
    uint8_t unused17[4];      // 0x04084
    uint32_t gorcl;           // 0x04088 Good Octets Received Count Low
    uint32_t gorch;           // 0x0408C Good Octets Received Count High
    uint32_t gotcl;           // 0x04090 Good Octets Transmitted Count Low
    uint32_t gotch;           // 0x04094 Good Octets Transmitted Count High
    uint8_t unused18[424];    // 0x04098

    uint32_t hlreg0;          // 0x04240 Highlander Control 0 Register
    uint8_t unused19[96];     // 0x04244
    uint32_t links;           // 0x042A4 Link Status Register
    uint8_t unused20[1704];   // 0x042A8

    uint32_t txpbthresh[8];   // 0x04950 + 0x4*n Tx Packet Buffer Threshold
    uint8_t unused21[272];    // 0x04970

    uint32_t dmatxctl;        // 0x04A80 DMA Tx Control
    uint8_t unused22[1532];   // 0x04A84

    uint32_t fctrl;           // 0x05080 Filter Control Register
    uint8_t unused23[3964];   // 0x05084

    tx_dma_regs_t tx_dma[64]; // 0x06000 Transmite Registers
    uint8_t unused24[4352];   // 0x07000

    uint32_t dtxmxszrq;       // 0x08100 DMA Tx TCP Max Allow Size Requests
    uint8_t unused25[1692];   // 0x08104

    uint32_t txdgpc;          // 0x087A0 DMA Good Tx Packet Counter
    uint32_t txdgbcl;         // 0x087A4 DMA Good Tx Byte Counter Low
    uint32_t txdgbch;         // 0x087A8 DMA Good Tx Byte Counter High
    uint8_t unused26[6740];   // 0x087AC

    rx_addr_t rx_addr[128];   // 0x0A200 + 0x8*n Receive Address
    uint8_t unused27[9728];   // 0x0A600

    uint32_t txpbsize[8];     // 0x0CC00 + 0x4*n Transmit Packet Buffer Size
    uint8_t unused28[13296];  // 0x0CC20

    uint32_t eec;             // 0x10010 EEPROM Mode Control Register
    uint8_t unused29[316];    // 0x10014
    uint32_t factps;          // 0x10150 Function Active and Power State to Manageability
} eth_regs_t;

struct pci_config_space {
    // Device Identification
    uint16_t vendor_id;           // 0x00: Vendor ID
    uint16_t device_id;           // 0x02: Device ID
    uint16_t command;             // 0x04: Command Register
    uint16_t status;              // 0x06: Status Register
    uint8_t revision_id;         // 0x08: Revision ID
    uint8_t prog_if;             // 0x09: Programming Interface
    uint8_t subclass;            // 0x0A: Sub Class Code
    uint8_t class_code;          // 0x0B: Base Class Code
    uint8_t cache_line_size;     // 0x0C: Cache Line Size
    uint8_t latency_timer;       // 0x0D: Latency Timer
    uint8_t header_type;         // 0x0E: Header Type
    uint8_t bist;                // 0x0F: Built-in Self Test

    // Base Address Registers (BARs)
    uint32_t bar[6];              // 0x10-0x27: Base Address Registers

    // Subsystem Information
    uint32_t cardbus_cis_ptr;     // 0x28: CardBus CIS Pointer
    uint16_t subsystem_vendor_id; // 0x2C: Subsystem Vendor ID
    uint16_t subsystem_device_id; // 0x2E: Subsystem Device ID
    uint32_t expansion_rom_addr;  // 0x30: Expansion ROM Base Address

    // Capabilities and Interrupts
    uint8_t cap_ptr;             // 0x34: Capabilities Pointer
    uint8_t reserved1[3];        // 0x35-0x37: Reserved
    uint32_t reserved2;           // 0x38-0x3B: Reserved
    uint8_t interrupt_line;      // 0x3C: Interrupt Line
    uint8_t interrupt_pin;       // 0x3D: Interrupt Pin
    uint8_t min_gnt;             // 0x3E: Min_Gnt
    uint8_t max_lat;             // 0x3F: Max_Lat

    // Capability list
    uint8_t cap_data[192];
};
