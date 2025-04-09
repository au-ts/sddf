/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* The reference manual used to acquire these values is:
 * i.MX 8M Plus Applications Processor Reference Manual.
 * Document number: IMX8MPRM.
 * Rev. 3, 08/2024.
 *
 * The CAN device is described under FlexCAN in section 11.8.
 */

/*
    There is a CAN 1 and CAN 2 but atm we just consider CAN 1.

    The docs give this as the base address - CAN1 base address: 308C_0000h --> is this the address of the device within the IoTGate memory?
*/

/* FlexCAN Module Configuration Register (MCR) - 11.8.5.2.2 */
#define MCR_MDIS                (1UL << 31)             /* Module Disable -- Controls whether FlexCAN is enabled or not - 0b = Enable, 1b = Disable */
#define MCR_FRZ                 (1UL << 30)             /* Freeze Enable -- Specifies behaviour when MCR[HALT] is enabled - 0b = Won't enter freeze, 1b = Will enter freeze*/
#define MCR_RFEN                (1UL << 29)             /* Rx FIFO Enable -- Specifies whether Rx FIFO is enabled or not - 0b = Disabled, 1b = Enabled */
#define MCR_HALT                (1UL << 28)             /* Halt FlexCAN -- Assertion puts FlexCAN into Freeze Mode - 0b = No freeze request, 1b = Freeze request */
#define MCR_NOTRDY              (1UL << 27)             /* FlexCAN Not Ready -- (Read-only) Indicates whether in operation mode or not. 0b = Normal, 1b = Not-operational */
#define MCR_WAKMSK              (1UL << 26)             /* Wake Up Interrupt Mask -- Enables wake up interrupt generation - 0b = Disabled, 1b = Enabled */
#define MCR_SOFTRST             (1UL << 25)             /* Soft Reset -- On assertion resets internal state machines/registers - 0b = No request, 1b = Reset request */
#define MCR_FRZACK              (1UL << 24)             /* Freeze Mode Acknowledge -- (Read-only) Indicates if in freeze mode - 0b = Not in freeze, 1b = In freeze */
#define MCR_SUPV                (1UL << 23)             /* Supervisor Mode -- Configures FlexCAN to be in supervisor or user mode. ob = User mode, 1b = Supervisor mode */
#define MCR_SLFWAK              (1UL << 22)             /* Self Wake Up -- Enable self wake up when in low power mode - 0b = Disabled, 1b = Enabled */
#define MCR_WRNEN               (1UL << 21)             /* Warning Interrupt Enable -- Enables generation of errors in status register - 0b - Disabled, 1b = Enabled */
#define MCR_LPMACK              (1UL << 20)             /* Low-Power Mode Acknowledge -- (Read-only) Indicates FlexCAN is in low-power mode - 0b = Not in mode, 1b = in mode */
#define MCR_WAKSRC              (1UL << 19)             /* Wake Up Source -- Whether low-pass filter applied to Rx - 0b = unfiltered, 1b = filtered */
#define MCR_DOZE                (1UL << 18)             /* Doze Mode Enable -- Determines whether can go low-power when Doze requested - 0b = Disabled, 1b = Enabled */
#define MCR_SRXDIS              (1UL << 17)             /* Self Reception Disable -- Whether FlexCAN receive frames transmitted by itself - 0b = Enabled, 1b = Disabled */
#define MCR_IRMQ                (1UL << 16)             /* Individual Rx Masking and Queue Enable -- Determines matching scheme for Rx - 0b = Disabled, 1b = Enabled */
#define MCR_DMA                 (1UL << 15)             /* DMA - Enable -- Controls whether DMA is enabled or not for Rx FIFO - 0b = Disabled, 1b = Enabled */
#define MCR_RESERVED0           (1UL << 14)             /* Reserved */
#define MCR_LPRIOEN             (1UL << 13)             /* Local Priority Enable -- Local priority control for backward compatibility - 0b = Disabled, 1b = Enabled */
#define MCR_AEN                 (1UL << 12)             /* Abort Enable -- Enables Tx abort mechanism - 0b = Disabled, 1b = Enabled */
#define MCR_FDEN                (1UL << 11)             /* CAN FD Operation Enable -- Enables CANFD operation - 0b = Disabled, 1b = Enabled */
#define MCR_RESERVED1           (1UL << 10)             /* Reserved */
#define MCR_IDAM(x)             (((x) & 3UL) << 8)      /* ID Acceptance Mode - 2-bit field identifies format of Rx FIFO ID filter table elements - See docs for details*/
#define MCR_RESERVED2           (1UL << 7)              /* Reserved */
#define MCR_MAXMB(x)            (((x) & 127UL) << 0)    /* Number Of The Last Message Buffer - 7-bit field defines number of last message buffers - See docs for details */

/* FlexCAN Control 1 Register (CTRL1) - 11.8.5.2.3 */
#define CTRL1_PRESDIV(x)        (((x) & 255UL) << 24)   /* Prescaler Division Factor */ 
#define CTRL1_RJW(x)            (((x) & 3UL) << 22)     /* Resync Jump Width */
#define CTRL1_PSEG1(x)          (((x) & 7UL) << 19)     /* Phase Segment 1 */
#define CTRL1_PSEG2(x)          (((x) & 7UL) << 16)     /* Phase Segment 2 */
#define CTRL1_BOFFMSK           (1UL << 15)             /* Bus Off Interrupt Mask */
#define CTRL1_ERRMSK            (1UL << 14)             /* Error Interrupt Mask */
#define CTRL1_CLKSRC            (1UL << 13)             /* CAN Engine Clock Source */
#define CTRL1_LPB               (1UL << 12)             /* Loop Back Mode */
#define CTRL1_TWRNMSK           (1UL << 11)             /* Tx Warning Interrupt Mask */
#define CTRL1_RWRNMSK           (1UL << 10)             /* Rx Warning Interrupt Mask */
#define CTRL1_RESERVED0         (1UL << 9)              /* Reserved */
#define CTRL1_RESERVED1         (1UL << 8)              /* Reserved */
#define CTRL1_SMP               (1UL << 7)              /* CAN Bit Sampling */
#define CTRL1_BOFFREC           (1UL << 6)              /* Bus Off Recovery */
#define CTRL1_TSYN              (1UL << 5)              /* Timer Sync */
#define CTRL1_LBUF              (1UL << 4)              /* Lowest Buffer Transmitted First */
#define CTRL1_LOM               (1UL << 3)              /* Listen-Only Mode */
#define CTRL1_PROPSEG(x)        (((x) & 7UL) << 0)      /* Propagation Segment */

/* Interrupt Flags 1 Register (IFLAG1) - 11.8.5.2.13 */
#define IFLAG1_BUF31TO8I    (16777215UL << 8)   /* Buffer MBi Interrupt -- Each bit flags the correpsonding message buffer interrupt for mb 8-31 */
#define IFLAG1_BUF7I        (1UL << 7)          /* Buffer MB7 Interrupt OR Rx FIFO Overflow -- 0b = no overflow, 1b = overflow occurred */                    
#define IFLAG1_BUF6I        (1UL << 6)          /* Buffer MB6 Interrupt OR Rx FIFO Warning -- 0b = no warning, 1b = warning FIFO almost full */
#define IFLAG1_BUF5I        (1UL << 5)          /* Buffer MB5 Interrupt OR Frames available in Rx FIFO -- 0b = no frames, 1b = frames available */
#define IFLAG1_BUF4TO1I     (15UL << 1)         /* Buffer MBi Interrupt OR Reserved -- these are reserved when FIFO in use */
#define IFLAG1_BUF0I        (1UL << 0)          /* Buffer MB0 Interrupt OR Clear FIFO bit - when asserted (set to 1b) empties the FIFO */

/* Additional Initialisation Registers -- these are only used to disable error correction at the moment */
#define CTRL2_ECRWRE    (1UL << 29) // Error correction configuration register write enable. Enables MECR to be updated 0 = disable update, 1 = enable update
#define MECR_ECRWRDIS   (1UL << 31) // Error configuration register write disable. Disables write on this register 0 = write is enabled, 1 = write is disabled
#define MECR_ECCDIS     (1UL << 8)  // Error correction disable. Disables memory detection and correction mechanism. 0 = enable correction, 1 = disable correction

/* Message Buffer Structure - 11.8.5.3  */
// Control bits
#define MB_CTRL_EDL             (1UL << 31)             /* Extended Data Length -- Distinguishes between CAN and CANFD frames */
#define MB_CTRL_BRS             (1UL << 30)             /* Bit Rate Switch -- Defines whether bit rate switch is in CANFD frame */
#define MB_CTRL_ESI             (1UL << 29)             /* Error State Indicator -- Indicates if transmitting node is error active or error passive */
#define MB_CTRL_RESERVED0       (1UL << 28)             /* Reserved */
#define MB_CTRL_CODE(x)         (((x) & 15UL) << 24)    /* Message Buffer Code -- See below for details*/
#define MB_CTRL_RESERVED1       (1UL << 23)             /* Reserved */
#define MB_CTRL_SRR             (1UL << 22)             /* Substitute Remote Request -- Used only in extended format*/
#define MB_CTRL_IDE             (1UL << 21)             /* ID Extended Bit -- Identifies whether frame is standard or extended */
#define MB_CTRL_RTR             (1UL << 20)             /* Remote Transmission Request -- Used for arbitration (see Table 11-186 for details)*/
#define MB_CTRL_DLC             (15UL << 16)            /* Length of Data Bytes -- Contains the length in bytes of the Rx or Tx data */
#define MB_CTRL_TIMESTAMP       (65535UL << 0)          /* Free-Running Counter Time Stamp -- Copy of the free-running timer value at Rx or Tx time */
// Id bits      
#define MB_ID_PRIO              (7UL << 29)             /* Local Priority -- Only used for Tx */
#define MB_ID_STD               (2047UL << 18)          /* Frame Identifier -- In standard only the 11 most significant bits are used */
#define MB_ID_EXT               (262143UL << 0)         /* Extended Identifier -- If extended is used both the 11 top and 18 bottom bits used for identifier */

/*
    Message Buffer Codes (Rx) -- See Table 11-186 for further details
    > 0000b: MB is inactive
    > 0100b: MB is active and empty
    > 0010b: MB is full
    > 0110b: MB is full and contains an overrun (written over a previous buffer)
    > 1010b: A frame configured to recognize remote request frame
    > If Code[0] == 1, FlexCAN is updating the contents of the MB and the CPU must not access it
*/

/* Message Buffer Setup */
#define FIFO_OUTPUT_BUFFER_OFFSET 0x80 // We read from message buffer 0 only for the FIFO 
struct message_buffer {
    uint32_t can_ctrl;
    uint32_t can_id;
    uint64_t data; // Note: this is fixed at 8 bytes as we're currently using standard CAN and not CANFD
};

/* IMX8 Clock Registers */
struct clock_registers {
    uint32_t base;
    uint32_t set;
    uint32_t clr;
    uint32_t tog;
};

/* FlexCAN Control Registers - these are mainly for configuring and interacting with the module. */
struct control_registers {
    uint32_t mcr;           /* 0h   Module Configuration Register */
    uint32_t ctrl1;         /* 4h   Control 1 Register */
    uint32_t timer;         /* 8h   Free Running Timer */
    uint32_t reserved_0;    /* Ch   Reserved */ 
    uint32_t rxmgmask;      /* 10h  Rx Mailboxes Global Mask Register */
    uint32_t rx14mask;      /* 14h  Rx 14 Mask Register */
    uint32_t rx15mask;      /* 18h  Rx 15 Mask Register */
    uint32_t ecr;           /* 1Ch  Error Counter */
    uint32_t esr1;          /* 20h  Error and Status 1 Register */
    uint32_t imask2;        /* 24h  Interrupt Masks 2 Register */
    uint32_t imask1;        /* 28h  Interrupt Masks 1 Register */
    uint32_t iflag2;        /* 2Ch  Interrupt Flags 2 Register */
    uint32_t iflag1;        /* 30h  Interrupt Flags 1 Register */
    uint32_t ctrl2;         /* 34h  Control 2 Register */
    uint32_t esr2;          /* 38h  Error and Status 2 Register */
    uint32_t reserved_1;    /* 3Ch  Reserved */
    uint32_t reserved_2;    /* 40h  Reserved */
    uint32_t crcr;          /* 44h  CRC Register */
    uint32_t rxfgmask;      /* 48h  Rx FIFO Global Mask Register */
    uint32_t rxfir;         /* 4Ch  Rx FIFO Information Register */
    uint32_t cbt;           /* 50h  CAN Bit Timing Register */
};

#define ACCEPTANCE_FILTER_REGISTER_OFFSET 0x880
struct acceptance_filter_registers {
    uint32_t rxmir[64];     /* 880h - 97Ch  FlexCAN Receive Mask Registers - these are used to specify IDs to filter for when receiving CAN messages */
};

/* FlexCAN Error Registers - these are for reading error occurrences */
#define ERROR_REGISTER_OFFSET 0xAE0
struct error_registers {
    uint32_t mecr;          /* AE0h Memory Error Control Register */
    uint32_t erriar;        /* AE4h Error Injection Address Register */
    uint32_t erridpr;       /* AE8h Error Injection Data Pattern Register */
    uint32_t errippr;       /* AECh Error Injection Parity Pattern Register */
    uint32_t rerrar;        /* AF0h Error Report Address Register */
    uint32_t rerrdr;        /* AF4h Error Report Data Register */
    uint32_t rerrsynr;      /* AF8h Error Report Syndrome Register */
    uint32_t errsr;         /* AFCh Error Status Register */
};

/* FlexCAN CANFD Registers - these are for enabling and using CANFD */
#define CANFD_REGISTER_OFFSET 0xC00
struct canfd_registers {
    uint32_t fdctrl;        /* C00h CAN FD Control Register */
    uint32_t fdcbt;         /* C04h CAN FD Bit Timing Register */
    uint32_t fdcrc;         /* C08h CAN FD CRC Register */
};