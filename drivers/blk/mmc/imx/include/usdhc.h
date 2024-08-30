/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

#include <sddf/util/util.h>

/* The driver is based on:

    [IMX8MDQLQRM]: i.MX8 Quad i.MX 8M Dual/8M QuadLite/8M Quad Applications Processors Reference Manual
                   Document Number: IMX8MDQLQRM, Rev 3.1, 06/2021.
                   https://www.nxp.com/webapp/Download?colCode=IMX8MDQLQRM
    [SD-PHY]:      SD Specifications Part 1 Physical Layer Simplified Specification.
                   Version 9.10, Dec. 2023.
                   https://www.sdcard.org/downloads/pls/
    [SD-HOST]:     SD Specifications Part A2 SD Host Controller Simplified Specification.
                   Version 4.20, July 2018.
                   https://www.sdcard.org/downloads/pls/
*/

/* [IMX8MDQLQRM] Section 10.3.7.1 uSDHC register descriptions.
   - uSDHC1 base address: 30B4_0000h
   - uSDHC2 base address: 30B5_0000h
   - uSDHC3 base address: 30B6_0000h

   Also, Section 7.1 Interrupts and DMA Events
   - uSDHC1 Enhanced SDHC Interrupt Request: 22 (use IRQ# 54)
   - uSDHC2 Enhanced SDHC Interrupt Request: 23 (use IRQ# 55)
*/
typedef struct imx_usdhc_regs {
    uint32_t ds_addr;              /* DMA System Address            (RW)   */
    uint32_t blk_att;              /* Block Attributes              (RW)   */
    uint32_t cmd_arg;              /* Command Argument              (RW)   */
    uint32_t cmd_xfr_typ;          /* Command Transfer Type         (RW)   */
    uint32_t cmd_rsp0;             /* Command Response0             (RO)   */
    uint32_t cmd_rsp1;             /* Command Response1             (RO)   */
    uint32_t cmd_rsp2;             /* Command Response2             (RO)   */
    uint32_t cmd_rsp3;             /* Command Response3             (RO)   */
    uint32_t data_buff_acc_port;   /* Data Buffer Access Port       (RW)   */
    uint32_t pres_state;           /* Present State                 (ROT)  */
    uint32_t prot_ctrl;            /* Protocol Control              (RW)   */
    uint32_t sys_ctrl;             /* System Control                (RW)   */
    uint32_t int_status;           /* Interrupt Status              (W1C)  */
    uint32_t int_status_en;        /* Interrupt Status Enable       (RW)   */
    uint32_t int_signal_en;        /* Interrupt Signal Enable       (RW)   */
    uint32_t autocmd12_err_status; /* Auto CMD12 Error Status       (RW)   */
    uint32_t host_ctrl_cap;        /* Host Controller Capabilities  (RW)   */
    uint32_t wtmk_lvl;             /* Watermark Level               (RW)   */
    uint32_t mix_ctrl;             /* Mixer Control                 (RW)   */
    uint32_t force_event;          /* Force Event                   (WORZ) */
    uint32_t adma_err_status;      /* ADMA Error Status             (RO)   */
    uint32_t adma_sys_addr;        /* ADMA System Address           (RW)   */
    uint32_t dll_ctrl;             /* DLL (Delay Line) Control      (RW)   */
    uint32_t dll_status;           /* DLL Status                    (RO)   */
    uint32_t clk_tune_ctrl_status; /* CLK Tuning Control and Status (RW)   */
    uint32_t strobe_dll_ctrl;      /* Strobe DLL control            (RW)   */
    uint32_t strobe_dll_status;    /* Strobe DLL status             (RO)   */
    uint32_t vend_spec;            /* Vendor Specific Register      (RW)   */
    uint32_t mmc_boot;             /* MMC Boot                      (RW)   */
    uint32_t vend_spec2;           /* Vendor Specific 2 Register    (RW)   */
    uint32_t tuning_ctrl;          /* Tuning Control                (RW)   */
    uint32_t cqe;                  /* Command Queue                 (ROZ)  */
} imx_usdhc_regs_t;

#define _LEN(start, end) ((end - start) + 1)
#define _MASK(start, end)  ((BIT(_LEN(start, end)) - 1) << (start))
#define _MASK_128(start, end)  ((__uint128_t)(BIT(_LEN(start, end)) - 1) << (start))

/* [IMX8MDQLQRM] Section 10.3.7.1.3 Block Attributes */
#define USDHC_BLK_ATT_BLKSIZE_SHIFT 0             /* Transfer block size  */
#define USDHC_BLK_ATT_BLKSIZE_MASK  _MASK(0, 12)  /* BLK_ATT[12-0]        */
#define USDHC_BLK_ATT_BLKCNT_SHIFT  16            /* Blocks count         */
#define USDHC_BLK_ATT_BLKCNT_MASK   _MASK(16, 31) /* BLK_ATT[16-31]        */

/* [IMX8MDQLQRM] Section 10.3.7.1.5 Command Transfer Type */
#define USDHC_CMD_XFR_TYP_CCCEN        BIT(19)       /* Command CRC check enable   */
#define USHDC_CMD_XFR_TYP_CICEN        BIT(20)       /* Command index check enable */
#define USDHC_CMD_XFR_TYP_DPSEL        BIT(21)       /* Data present select        */
#define USDHC_CMD_XFR_TYP_RSPTYP_SHIFT 16            /* Response type select       */
#define USDHC_CMD_XFR_TYP_RSPTYP_MASK  _MASK(16, 17) /* RSPTYP[17-16]              */
#define USDHC_CMD_XFR_TYP_CMDINX_SHIFT 24            /* Command index              */
#define USDHC_CMD_XFR_TYP_CMDINX_MASK  _MASK(24, 29) /* CMDINX[29-24]              */

#define USDHC_CMD_XFR_TYP_RSPTYP_NONE  0b00          /* No response                    */
#define USDHC_CMD_XFR_TYP_RSPTYP_L136  0b01          /* Response length 136            */
#define USDHC_CMD_XFR_TYP_RSPTYP_L48   0b10          /* Response length 48             */
#define USDHC_CMD_XFR_TYP_RSPTYP_L48B  0b11          /* Response length 48, check busy */

/* [IMX8MDQLQRM] Section 10.3.7.1.11 Present State */
#define USDHC_PRES_STATE_CIHB  BIT(0)  /* Command inhibit (CMD) */
#define USDHC_PRES_STATE_CDIHB BIT(1)  /* Command inhibit (DATA) */
#define USDHC_PRES_STATE_DLA   BIT(2)  /* Data line active */
#define USDHC_PRES_STATE_SDSTB BIT(3)  /* SD clock stable */
#define USDHC_PRES_STATE_CINST BIT(16) /* Card inserted. */
#define USDHC_PRES_STATE_DLSL0 BIT(24) /* DATA[0] line signal level */

/* [IMX8MDQLQRM] Section 10.3.7.1.12 Protocol Control */
#define USDHC_PROT_CTRL_DTW_SHIFT    1             /* Data transfer width.   */
#define USDHC_PROT_CTRL_DTW_MASK     _MASK(1, 2)   /* 2 Bits: PROT_CTRL[2-1] */
#define USDHC_PROT_CTRL_EMODE_SHIFT  4             /* Endian mode.           */
#define USDHC_PROT_CTRL_EMODE_MASK   _MASK(4, 5)   /* 2 Bits: PROT_CTRL[5-4] */
#define USDHC_PROT_CTRL_DMASEL_SHIFT 8             /* DMA select.            */
#define USDHC_PROT_CTRL_DMASEL_MASK  _MASK(8, 9)   /* 2 Bits: PROT_CTRL[9-8] */

#define USDHC_PROT_CTRL_DTW_1_BIT      0b00
#define USDHC_PROT_CTRL_DTW_4_BIT      0b01
#define USDHC_PROT_CTRL_DTW_8_BIT      0b10

#define USDHC_PROT_CTRL_EMODE_BIG      0b00
#define USDHC_PROT_CTRL_EMODE_HWBIG    0b01
#define USDHC_PROT_CTRL_EMODE_LITTLE   0b10

#define USDHC_PROT_CTRL_DMASEL_SIMPLE  0b00
#define USDHC_PROT_CTRL_DMASEL_ADMA1   0b01
#define USDHC_PROT_CTRL_DMASEL_ADMA2   0b10

/* [IMX8MDQLQRM] Section 10.3.7.1.13 System Control*/
#define USDHC_SYS_CTRL_RSTA  BIT(24)  /* Software reset for all */
#define USDHC_SYS_CTRL_RSTC  BIT(25)  /* Software reset for CMD line */
#define USDHC_SYS_CTRL_RSTD  BIT(26)  /* Software reset for data line */
#define USDHC_SYS_CTRL_INITA BIT(27)  /* Initialization active */
#define USDHC_SYS_CTRL_RSTT  BIT(28)  /* Reset tuning */

#define USDHC_SYS_CTRL_DTOCV_SHIFT   16            /* Data timeout counter value */
#define USDHC_SYS_CTRL_DTOCV_MASK    _MASK(16, 19) /* 4 bits; SYS_CTRL[19-16]    */
#define USDHC_SYS_CTRL_SDCLKFS_SHIFT 8             /* SDCLK frequency select     */
#define USDHC_SYS_CTRL_SDCLKFS_MASK  _MASK(8, 15)  /* 8 bits; SYS_CTRL[8-15]     */
#define USDHC_SYS_CTRL_DVS_SHIFT     4             /* Divisor                    */
#define USDHC_SYS_CTRL_DVS_MASK      _MASK(4, 7)   /* 4 bits; SYS_CTRL[4-7]      */

/* [IMX8MDQLQRM] Section 10.3.7.1.14 Interrupt Status */
#define USDHC_INT_STATUS_CC    BIT(0)  /* Command complete. */
#define USDHC_INT_STATUS_TC    BIT(1)  /* Transfer complete. */
#define USDHC_INT_STATUS_CTOE  BIT(16) /* Command timeout error. */
#define USDHC_INT_STATUS_CCE   BIT(17) /* Command CRC error. */
#define USDHC_INT_STATUS_CEBE  BIT(18) /* Command end bit error */
#define USDHC_INT_STATUS_CIE   BIT(19) /* Command index error. */
#define USDHC_INT_STATUS_DTOE  BIT(20) /* Data timeout error. */
#define USDHC_INT_STATUS_AC12E BIT(24) /* Auto CMD12 error. */

/* [IMX8MDQLQRM] Section 10.3.7.1.15 Interrupt Status Enable (used ones only) */
#define USDHC_INT_STATUS_EN_CCSEN    BIT(0)   /* Command complete status enable */
#define USDHC_INT_STATUS_EN_TCSEN    BIT(1)   /* Transfer complete status enable */
#define USDHC_INT_STATUS_EN_CINSSEN  BIT(6)   /* Card insertion status enable */
#define USDHC_INT_STATUS_EN_CRMSEN   BIT(7)   /* Card removal status enable */
#define USDHC_INT_STATUS_EN_CTOESEN  BIT(16)  /* Command timeout error status enable */
#define USDHC_INT_STATUS_EN_CCESEN   BIT(17)  /* Command CRC error status enable */
#define USDHC_INT_STATUS_EN_CEBESEN  BIT(18)  /* Command end bit error status enable */
#define USDHC_INT_STATUS_EN_CIESEN   BIT(19)  /* Command index error status enable */
#define USDHC_INT_STATUS_EN_DTOESEN  BIT(20)  /* Data timeout error status enable*/
#define USDHC_INT_STATUS_EN_DCSESEN  BIT(21)  /* Data CRC error status enable */
#define USDHC_INT_STATUS_EN_DEBESEN  BIT(22)  /* Data end bit error status enable */
#define USDHC_INT_STATUS_EN_AC12ESEN BIT(24)  /* Auto CMD12 error status enable */
#define USDHC_INT_STATUS_EN_DMAESEN  BIT(28)  /* DMA error status enable */

/* [IMX8MDQLQRM] Section 10.3.7.1.16 Interrupt Signal Enable (used ones only) */
#define USDHC_INT_SIGNAL_EN_CCIEN    BIT(0)   /* Command complete interrupt enable */
#define USDHC_INT_SIGNAL_EN_TCIEN    BIT(1)   /* Transfer complete interrupt enable */
#define USDHC_INT_SIGNAL_EN_CINSIEN  BIT(6)   /* Card insertion interrupt enable */
#define USDHC_INT_SIGNAL_EN_CRMIEN   BIT(7)   /* Card removal interrupt enable */
#define USDHC_INT_SIGNAL_EN_CTOEIEN  BIT(16)  /* Command timeout error interrupt enable */
#define USDHC_INT_SIGNAL_EN_CCEIEN   BIT(17)  /* Command CRC error interrupt enable */
#define USDHC_INT_SIGNAL_EN_CEBEIEN  BIT(18)  /* Command end bit error interrupt enable */
#define USDHC_INT_SIGNAL_EN_CIEIEN   BIT(19)  /* Command index error interrupt enable */
#define USDHC_INT_SIGNAL_EN_DTOEIEN  BIT(20)  /* Data timeout error interrupt enable*/
#define USDHC_INT_SIGNAL_EN_DCSEIEN  BIT(21)  /* Data CRC error interrupt enable */
#define USDHC_INT_SIGNAL_EN_DEBEIEN  BIT(22)  /* Data end bit error interrupt enable */
#define USDHC_INT_SIGNAL_EN_AC12EIEN BIT(24)  /* Auto CMD12 error interrupt enable */
#define USDHC_INT_SIGNAL_EN_DMAEIEN  BIT(28)  /* DMA error interrupt enable */

/* [IMX8MDQLQRM] Section 10.3.7.1.18 Host Controller Capabilities */
#define USDHC_HOST_CTRL_CAP_DMAS  BIT(22)  /* DMA Support */
#define USDHC_HOST_CTRL_CAP_VS33  BIT(24)  /* Voltage support 3.3 V */

/* [IMX8MDQLQRM] Section 10.3.7.1.20 Mixer Control */
#define USDHC_MIX_CTRL_DMAEN  BIT(0)  /* DMA enable */
#define USDHC_MIX_CTRL_BCEN   BIT(1)  /* Block count enable */
#define USDHC_MIX_CTRL_AC12EN BIT(2)  /* Auto CMD12 enable */
#define USDHC_MIX_CTRL_DTDSEL BIT(4)  /* Data transfer direction select (1 = read) */
#define USDHC_MIX_CTRL_MSBSEL BIT(5)  /* Mult / Single block select */

/* [IMX8MDQLQRM] Section 10.3.7.1.29 Vendor Specific Register */
#define USDHC_VEND_SPEC_FRC_SDCLK_ON BIT(8) /* Force CLK output active. */


/*
    Below this point is generic non-imx specific SD items from [SD-PHY].
*/

/* [SD-PHY] Section 4.9 Responses */
typedef enum __attribute__((__packed__))
{
    RespType_None = 0,
    RespType_R1,
    RespType_R1b,
    RespType_R2,
    RespType_R3,
    RespType_R4,
    RespType_R5,
    RespType_R6,
    RespType_R7,
}
response_type_t;

/* An arbitrary sd_cmd_t type for passing commands */
typedef struct {
    uint8_t cmd_index;
    response_type_t cmd_response_type;
    bool is_app_cmd;
    bool data_present;
} sd_cmd_t;
#define _SD_CMD_DEF(number, rtype, ...)  (sd_cmd_t){.cmd_index = (number), .cmd_response_type = (rtype), .is_app_cmd = false, ##__VA_ARGS__}
#define _SD_ACMD_DEF(number, rtype) (sd_cmd_t){.cmd_index = (number), .cmd_response_type = (rtype), .is_app_cmd = true, .data_present = false}

/* [SD-PHY] Section 4.7.4 Detailed Command Description */
#define SD_CMD0_GO_IDLE_STATE        _SD_CMD_DEF(0, RespType_None)  /* [31:0] stuff bits */
#define SD_CMD2_ALL_SEND_CID         _SD_CMD_DEF(2, RespType_R2)    /* [31:0] stuff bits */
#define SD_CMD3_SEND_RELATIVE_ADDR   _SD_CMD_DEF(3, RespType_R6)    /* [31:0] stuff bits */
#define SD_CMD7_CARD_SELECT          _SD_CMD_DEF(7, RespType_R1b)   /* [31:16] RCA, [15:0] stuff bits */
#define SD_CMD8_SEND_IF_COND         _SD_CMD_DEF(8, RespType_R7)    /* [31:12] zeroed, [11:8] VHS, [7:0] check pattern */
#define SD_CMD9_SEND_CSD             _SD_CMD_DEF(9, RespType_R2)    /* [31:16] RCA, [15:0] stuff bits */
#define SD_CMD13_SEND_STATUS         _SD_CMD_DEF(13, RespType_R1)   /* [31:16] RCA, [15:0] stuff bits */
#define SD_CMD16_SET_BLOCKLEN        _SD_CMD_DEF(16, RespType_R1)   /* [31:0] block length */
#define SD_CMD18_READ_MULTIPLE_BLOCK _SD_CMD_DEF(18, RespType_R1, .data_present = true)  /* [31:0] data address */
#define SD_CMD25_WRITE_MULTIPLE_BLOCK  _SD_CMD_DEF(25, RespType_R1, .data_present = true)  /* [31:0] data address */
#define SD_CMD55_APP_CMD             _SD_CMD_DEF(55, RespType_R1)   /* [31:16] RCA, [15:0] stuff bits */

#define SD_ACMD41_SD_SEND_OP_COND    _SD_ACMD_DEF(41, RespType_R3)  /* [31] zero, [30] host capacity status (CCS), [29] eSD reserved , [28] XPC, [27:25] zeroed, [24] S18R, [23:0] Vdd Voltage Window (host) */
#define SD_ACMD51_SEND_SCR           _SD_ACMD_DEF(51, RespType_R1)  /* [31:0] stuff bits */

/* [SD-PHY] Section 4.9.5 R6 Published RCA Response */
#define SD_RCA_SHIFT 16               /* New published RCA of the card */
#define SD_RCA_MASK  _MASK(16, 31)    /* RCA: [31:16]                  */

/* [SD-PHY] Section 4.9.6 R7 Card Interface Condition / Section 4.3.13 CMD8  */
#define SD_IF_COND_CHECK_SHIFT 0            /* Check pattern, to be echoed   */
#define SD_IF_COND_CHECK_MASK  _MASK(0, 7)  /* Bits [7:0]                    */
#define SD_IF_COND_VHS_SHIFT   8            /* Voltage supplied; Table 4-18. */
#define SD_IF_COND_VHS_MASK    _MASK(8, 11) /* 0001b = 2.7-3.6V; or reserved */
#define SD_IF_COND_VHS27_36    0b0001       /* VHS = 2.7-3.6V               */

/* [SD-PHY] Section 4.10.1 Card Status */
#define SD_CARD_STATUS_APP_CMD  BIT(5)   /* The card will expect ACMD */

/* [SD-PHY] Section 5.1 OCR Register */
#define SD_OCR_VDD27_28         BIT(15)  /* Vdd supports 2.7–2.8V */
#define SD_OCR_VDD28_29         BIT(16)  /* Vdd supports 2.8–2.9V */
#define SD_OCR_VDD29_30         BIT(17)  /* Vdd supports 2.9–3.0V */
#define SD_OCR_VDD30_31         BIT(18)  /* Vdd supports 3.0–3.1V */
#define SD_OCR_VDD31_32         BIT(19)  /* Vdd supports 3.1–3.2V */
#define SD_OCR_VDD32_33         BIT(20)  /* Vdd supports 3.2–3.3V */
#define SD_OCR_VDD33_34         BIT(21)  /* Vdd supports 3.3–3.4V */
#define SD_OCR_VDD34_35         BIT(22)  /* Vdd supports 3.4–3.5V */
#define SD_OCR_VDD35_36         BIT(23)  /* Vdd supports 3.5–3.6V */
#define SD_OCR_CCS              BIT(30)  /* Card Capacity Status (CCS) */
#define SD_OCR_HCS              BIT(30)  /* Host Capacity Status (HCS) */
#define SD_OCR_POWER_UP_STATUS  BIT(31)  /* Card power up status bit (busy) */

/* [SD-PHY] Section 5.3.1 CSD Register */
#define SD_CSD_CSD_STRUCTURE_SHIFT    126             /* CSD Structure (version)      */
#define SD_CSD_CSD_STRUCTURE_MASK     _MASK_128(126, 127) /* CSD-slice: [127:126]         */

/* [SD-PHY] Section 5.3.2 CSD Register (CSD Version 1.0) */
#define SD_CSD_V1_READ_BL_LEN_SHIFT   80                 /* max. read data block length  */
#define SD_CSD_V1_READ_BL_LEN_MASK    _MASK_128(80, 83)  /* CSD-slice: [83:80]           */
#define SD_CSD_V1_C_SIZE_MULT_SHIFT   47                 /* device size multiplier       */
#define SD_CSD_V1_C_SIZE_MULT_MASK    _MASK_128(47, 49)  /* CSD-slice: [49:47]           */
#define SD_CSD_V1_C_SIZE_SHIFT        62                 /* device size (user area size) */
#define SD_CSD_V1_C_SIZE_MASK         _MASK_128(62, 73)  /* CSD-slice: [75:48]           */

/* [SD-PHY] Section 5.3.3 CSD Register (CSD Version 2.0) */
#define SD_CSD_V2_C_SIZE_SHIFT        48                 /* device size (user area size) */
#define SD_CSD_V2_C_SIZE_MASK         _MASK_128(48, 69)  /* CSD-slice: [69:48]           */

/* [SD-PHY] Section 5.3.4 CSD Register (CSD Version 3.0) */
#define SD_CSD_V3_C_SIZE_SHIFT        48                 /* device size (user area size) */
#define SD_CSD_V3_C_SIZE_MASK         _MASK_128(48, 75)  /* CSD-slice: [75:48]           */


/* [SD-HOST] Section 3.2.3 Clock Frequency Change - timeout is 150ms */
#define SD_CLOCK_STABLE_TIMEOUT (150 * NS_IN_MS)
/* [SD-PHY] 4.2.3.1 Initialization Command - timeout is 1s */
#define SD_INITIALISATION_TIMEOUT (1 * NS_IN_S)

/* [SD-PHY] Section 4.10.1 Card Status Field 'CURRENT_STATE',
       and Section 4.1 - Table 4-1. */
typedef enum sd_card_state {
    CardStateIdle = 0,  /* Idle State           (Card Identification) */
    CardStateReady = 1, /* Ready State          (Card Identification) */
    CardStateIdent = 2, /* Identification State (Card Identification) */
    CardStateStdby = 3, /* Stand-by State       (Data Transfer)       */
    CardStateTran = 4,  /* Transfer State       (Data Transfer)       */
    CardStateData = 5,  /* Sending-data State   (Data Transfer)       */
    CardStateRcv = 6,   /* Receive-data State   (Data Transfer)       */
    CardStatePrg = 7,   /* Programming State    (Data Transfer)       */
    CardStateDis = 8,   /* Disconnect State     (Data Transfer)       */

    /* 9-15 reserved */
} sd_card_state_t;

#define KHZ (1000)
#define MHZ (1000 * KHZ)

typedef enum sd_clock_freq {
    /* [SD-PHY] 4.2.1 Card Reset "The cards are initialized... 400KHz clock frequency" */
    ClockSpeedIdentify_400KHz = 400 * KHZ,

    // TODO: Higher speeds are currently never used.
    // ClockSpeedDefaultSpeed_25MHz = 25 * MHZ,
} sd_clock_freq_t;
