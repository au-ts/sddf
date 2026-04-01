/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * This driver is based on the Linux driver:
 *      drivers/net/ethernet/broadcom/genet/bcmgenet.c
 *      which is: Copyright (c) 2014-2017 Broadcom
 *
 * Also referred to:
 *      https://github.com/u-boot/u-boot/blob/master/drivers/net/bcmgenet.c
 *      https://github.com/RT-Thread/rt-thread/blob/master/bsp/raspberry-pi/raspi4-32/driver/drv_eth.c
 *      BCM54213PE Datasheet
 */

#pragma once

#define PORT_MODE_EXT_GPHY 3
#define CMD_PROMISC                 BIT(4)
#define CMD_SW_RESET                BIT(13)
#define CMD_LCL_LOOP_EN             BIT(15)

#define GENET_PHY_ID 1
#define MDIO_START_BUSY             BIT(29)
#define MDIO_READ_FAIL              BIT(28)
#define MDIO_RD                     (2 << 26)
#define MDIO_WR                     BIT(26)
#define MDIO_PMD_SHIFT              (21)
#define MDIO_PMD_MASK               (0x1f)
#define MDIO_REG_SHIFT              (16)
#define MDIO_REG_MASK               (0x1f)

#define CMD_TX_EN                   BIT(0)
#define CMD_RX_EN                   BIT(1)
#define UMAC_SPEED_10               (0)
#define UMAC_SPEED_100              (1)
#define UMAC_SPEED_1000             (2)
#define UMAC_SPEED_2500             (3)
#define CMD_SPEED_SHIFT             (2)
#define CMD_SPEED_MASK              (3)
#define CMD_SW_RESET                BIT(13)
#define CMD_LCL_LOOP_EN             BIT(15)

#define GENET_IRQ_TXDMA_DONE           BIT(16)
#define GENET_IRQ_RXDMA_DONE           BIT(13)

#define RGMII_LINK                  BIT(4)
#define RGMII_MODE_EN               BIT(6)
#define ID_MODE_DIS                 BIT(16)

#define MIB_RESET_RX                BIT(0)
#define MIB_RESET_RUNT              BIT(1)
#define MIB_RESET_TX                BIT(2)

/* Body(1500) + EH_SIZE(14) + VLANTAG(4) + BRCMTAG(6) + FCS(4) = 1528.
 * MTU must be a multiple of 256, so we set ENET_PAD to 8.
 * RSB/TSB (64Bytes) is not included.
 */
#define ETH_DATA_LEN                (1500)
#define ETH_HLEN                    (14)
#define VLAN_HLEN                   (4)
#define ETH_FCS_LEN                 (4)
#define ENET_BRCM_TAG_LEN           (6)
#define ENET_PAD                    (8)
#define ENET_MAX_MTU_SIZE        (ETH_DATA_LEN + ETH_HLEN +     \
                                  VLAN_HLEN + ENET_BRCM_TAG_LEN +   \
                                  ETH_FCS_LEN + ENET_PAD)

#define GENET_RBUF_OFF              (0x0300)
#define RBUF_TBUF_SIZE_CTRL         (GENET_RBUF_OFF + 0xb4)
#define RBUF_CTRL                   (GENET_RBUF_OFF + 0x00)
#define RBUF_ALIGN_2B               BIT(1)

#define RBUF_64B_EN                 BIT(0)
#define RBUF_CTRL_CHKSUM_EN         BIT(0)
#define TBUF_64B_EN                 BIT(0)
#define TBUF_CTRL_CHKSUM_EN         BIT(0)

/* Tx/Rx Dma Descriptor common bits */
#define DMA_EN                       BIT(0)
#define DMA_RING_BUF_EN_SHIFT        (0x01)
#define DMA_RING_BUF_EN_MASK         (0xffff)
#define DMA_BUFLENGTH_MASK           (0x0fff)
#define DMA_BUFLENGTH_SHIFT          (16)
#define DMA_RING_SIZE_SHIFT          (16)
#define DMA_OWN                      (0x8000)
#define DMA_EOP                      (0x4000)
#define DMA_SOP                      (0x2000)
#define DMA_WRAP                     (0x1000)
#define DMA_MAX_BURST_LENGTH         (0x8)
/* Tx specific DMA descriptor bits */
#define DMA_TX_UNDERRUN              (0x0200)
#define DMA_TX_APPEND_CRC            (0x0040)
#define DMA_TX_OW_CRC                (0x0020)
#define DMA_TX_DO_CSUM               (0x0010)
#define DMA_TX_CHKSUM_EN             BIT(15)
#define DMA_TX_QTAG_SHIFT            (7)

#define DMA_TIMEOUT_MASK             0xFFFF

#define DEFAULT_Q                    0x10
#define RING_INDEX_CAPACITY          0x10000

#define BCM54213PE_MII_CONTROL                 (0x00)
#define BCM54213PE_MII_STATUS                  (0x01)
#define BCM54213PE_PHY_IDENTIFIER_HIGH         (0x02)
#define BCM54213PE_PHY_IDENTIFIER_LOW          (0x03)

#define BCM54213PE_AUTO_NEGOTIATION_ADV        (0x04)
#define BCM54213PE_AUTO_NEGOTIATION_LINK       (0x05)
#define BCM54213PE_AUTO_NEGOTIATION_EXPANSION  (0x06)

#define BCM54213PE_NEXT_PAGE_TX                (0x07)

#define BCM54213PE_PARTNER_RX                  (0x08)

#define BCM54213PE_CONTROL                     (0x09)
#define BCM54213PE_STATUS                      (0x0A)

#define BCM54213PE_IEEE_EXTENDED_STATUS        (0x0F)
#define BCM54213PE_PHY_EXTENDED_CONTROL        (0x10)
#define BCM54213PE_PHY_EXTENDED_STATUS         (0x11)

#define BCM54213PE_RECEIVE_ERROR_COUNTER       (0x12)
#define BCM54213PE_FALSE_C_S_COUNTER           (0x13)
#define BCM54213PE_RECEIVE_NOT_OK_COUNTER      (0x14)

#define BCM54213PE_VERSION_B1                   (0x600d84a2)
#define BCM54213PE_VERSION_X                    (0x600d84a0)

//BCM54213PE_MII_CONTROL
#define MII_CONTROL_PHY_RESET                   BIT(15)
#define MII_CONTROL_AUTO_NEGOTIATION_ENABLED    BIT(12)
#define MII_CONTROL_AUTO_NEGOTIATION_RESTART    BIT(9)
#define MII_CONTROL_PHY_FULL_DUPLEX             BIT(8)
#define MII_CONTROL_SPEED_SELECTION             BIT(6)

//BCM54213PE_MII_STATUS
#define MII_STATUS_LINK_UP                      BIT(2)
#define MII_STATUS_AUTO_NEGOTIATION_COMPLETE    BIT(5)

//BCM54213PE_CONTROL
#define CONTROL_FULL_DUPLEX_CAPABILITY          BIT(9)
#define CONTROL_HALF_DUPLEX_CAPABILITY          BIT(8)

struct genet_dma_desc {
    uint32_t status;
    uint32_t addr_lo;
    uint32_t addr_hi;
};

#define NUM_DESCS                    256
#define DESC_SIZE                    sizeof(struct genet_dma_desc)

struct genet_dma_ring_rx {
    uint32_t write_ptr;               // 0x00
    uint32_t unused1;                 // 0x04
    uint32_t prod_index;              // 0x08
    uint32_t cons_index;              // 0x0C
    uint32_t buf_size;                // 0x10
    uint32_t start_addr;              // 0x14
    uint32_t unused2;                 // 0x18
    uint32_t end_addr;                // 0x1C
    uint32_t unused3;                 // 0x20
    uint32_t mbuf_done_thresh;        // 0x24
    uint32_t xon_xoff_thresh;         // 0x28
    uint32_t read_ptr;                // 0x2C
    uint8_t unused4[16];              // 0x30-0x40
};

struct genet_dma_ring_tx {
    uint32_t read_ptr;                // 0x00
    uint32_t unused1;                 // 0x04
    uint32_t cons_index;              // 0x08
    uint32_t prod_index;              // 0x0C
    uint32_t buf_size;                // 0x10
    uint32_t start_addr;              // 0x14
    uint32_t unused2;                 // 0x18
    uint32_t end_addr;                // 0x1C
    uint32_t unused3;                 // 0x20
    uint32_t mbuf_done_thresh;        // 0x24
    uint32_t flow_period;             // 0x28
    uint32_t write_ptr;               // 0x2C
    uint8_t unused4[16];              // 0x30-0x40
};

typedef struct genet_dma_ring {
    uint8_t x[64];
} genet_dma_ring_t;

struct genet_dma {
    struct genet_dma_desc descs[NUM_DESCS];               // 0x000
    genet_dma_ring_t default_rings[DEFAULT_Q];            // 0xC00-0x1000
    genet_dma_ring_t ring;                                // 0x1000-0x1040
    uint32_t ring_cfg;                                    // 0x1040
    uint32_t ctrl;                                        // 0x1044
    uint8_t unused1[4];                                   // 0x1048
    uint32_t burst_size;                                  // 0x104C
    uint8_t unused3[92];                                  // 0x1050-0x10AC
    uint32_t ring16_timeout;                              // 0x10AC
};

struct genet_regs {
    uint32_t sys_rev_ctrl;              // 0x00
    uint32_t sys_port_ctrl;             // 0x04
    uint32_t sys_rbuf_flush_ctrl;       // 0x08
    uint32_t sys_tbuf_flush_ctrl;       // 0x0C
    uint8_t sys_unused[112];            // 0x10-0x80
    uint32_t ext_pwr_mgmt;              // 0x80
    uint8_t ext_unused1[8];             // 0x84-0x8C
    uint32_t ext_rgmii_oob_ctrl;        // 0x8C
    uint8_t ext_unused2[12];            // 0x90-0x9C
    uint32_t ext_gphy_ctrl;             // 0x9C
    uint8_t ext_unused3[352];           // 0xA0-0x200
    uint32_t intrl2_0_cpu_stat;         // 0x200
    uint32_t intrl2_0_cpu_set;          // 0x204
    uint32_t intrl2_0_cpu_clear;        // 0x208
    uint32_t intrl2_0_cpu_stat_mask;    // 0x20C
    uint32_t intrl2_0_cpu_set_mask;     // 0x210
    uint32_t intrl2_0_cpu_clear_mask;   // 0x214
    uint8_t intrl2_0_unused2[40];       // 0x218-0x240
    uint32_t intrl2_1_cpu_stat;         // 0x240
    uint32_t intrl2_1_cpu_set;          // 0x244
    uint32_t intrl2_1_cpu_clear;        // 0x248
    uint32_t intrl2_1_cpu_stat_mask;    // 0x24C
    uint32_t intrl2_1_cpu_set_mask;     // 0x250
    uint32_t intrl2_1_cpu_clear_mask;   // 0x254
    uint8_t intrl2_unused2[168];        // 0x258-0x300
    uint32_t rbuf_ctrl;                 // 0x300
    uint8_t rbuf_unused1[176];          // 0x304-0x3B4
    uint32_t rbuf_tbuf_size_ctrl;       // 0x3B4
    uint8_t rbuf_unused2[584];          // 0x3B8-0x600
    uint32_t tbuf_ctrl;                 // 0x600
    uint32_t tbuf_ck_ctrl;              // 0x604
    uint8_t tbuf_unused[504];           // 0x608-0x800
    uint8_t umac_unused1[8];            // 0x800-0x808
    uint32_t umac_cmd;                  // 0x808
    uint32_t umac_mac0;                 // 0x80C
    uint32_t umac_mac1;                 // 0x810
    uint32_t umac_max_frame_len;        // 0x814
    uint8_t umac_unused2[796];          // 0x818-0xB34
    uint32_t umac_tx_flush;             // 0xB34
    uint8_t umac_unused3[584];          // 0xB38-0xD80
    uint32_t umac_mib_ctrl;             // 0xD80
    uint8_t umac_unused4[144];          // 0xD84-0xE14
    uint32_t umac_mdio_cmd;             // 0xE14
    uint8_t unused1[56];                // 0xE18-0xE50
    uint32_t umac_mdf_ctrl;             // 0xE50
    uint8_t unused2[4524];              // 0xE54-0x2000
    struct genet_dma dma_rx;            // 0x2000-0x30B0
    uint8_t unused3[3920];              // 0x30B0-0x4000
    struct genet_dma dma_tx;            // 0x4000
};

#define MBOX_REQUEST    0
#define MBOX_TAG_HARDWARE_GET_MAC_ADDRESS  0x00010003
#define MBOX_TAG_HARDWARE_GET_CLK_RATE     0x00030002
#define MBOX_TAG_HARDWARE_SET_CLK_RATE     0x00038002
#define MBOX_TAG_LAST           0
#define MBOX_ADDR       0x08000000
#define MBOX_RESPONSE   0x80000000
#define MBOX_FULL       0x80000000
#define MBOX_EMPTY      0x40000000

struct mbox_regs {
    uint32_t read;                   // 0x00
    uint32_t unused1[3];             // 0x04-0x10
    uint32_t poll;                   // 0x10
    uint32_t sender;                 // 0x14
    uint32_t status;                 // 0x18
    uint32_t config;                 // 0x1C
    uint32_t write;                  // 0x20
};

/* TSB structure for BCM GENET hardware checksum offload */
struct bcmgenet_tsb {
    uint32_t length_status;      /* length and peripheral status */
    uint32_t ext_status;         /* Extended status*/
    uint32_t rx_csum;            /* partial rx checksum */
    uint32_t unused1[9];         /* unused */
    /**
     * Tx checksum info.
     * Bits 14-0 contain the checksum destination offset.
     * Bit 15 calculate UDP/TCP checksum.
     * Bits 30-16 contain the offset of first byte to be checksummed.
     * Bit 31 enables checksum offloading.
     * Note the transport layer header must be initialised with pseudo header checksum.
     */
    uint32_t tx_csum_info;
    uint32_t unused2[3];         /* unused */
};

#define CHECKSUM_TSB_LENGTH sizeof(struct bcmgenet_tsb)
