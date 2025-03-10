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
#define MCR_DISABLE         (1UL << 31) /* Module Disable -- Controls whether FlexCAN is enabled or not - 0b = Enable, 1b = Disable */
#define MCR_FREEZE          (1UL << 30) /* Freeze Enable -- Specifies behaviour when MCR[HALT] is enabled - 0b = Won't enter freeze, 1b = Will enter freeze*/
#define MCR_RX_FIFO         (1UL << 29) /* Rx FIFO Enable -- Specifies whether Rx FIFO is enabled or not - 0b = Disabled, 1b = Enabled */
#define MCR_HALT            (1UL << 28) /* Halt FlexCAN -- Assertion puts FlexCAN into Freeze Mode - 0b = No freeze request, 1b = Freeze request */
#define MCR_NOT_READY       (1UL << 27) /* FlexCAN Not Ready -- (Read-only) Indicates whether in operation mode or not. 0b = Normal, 1b = Not-operational */
#define MCR_WAKE_INT_MASK   (1UL << 26) /* Wake Up Interrupt Mask -- Enables wake up interrupt generation - 0b = Disabled, 1b = Enabled */
#define MCR_SOFT_RESET      (1UL << 25) /* Soft Reset -- On assertion resets internal state machines/registers - 0b = No request, 1b = Reset request */
#define MCR_FREEZE_ACK      (1UL << 24) /* Freeze Mode Acknowledge -- (Read-only) Indicates if in freeze mode - 0b = Not in freeze, 1b = In freeze */
#define MCR_SUPERVISOR      (1UL << 23) /* Supervisor Mode -- Configures FlexCAN to be in supervisor or user mode. ob = User mode, 1b = Supervisor mode */
#define MCR_SELF_WAKE       (1UL << 22) /* Self Wake Up -- Enable self wake up when in low power mode - 0b = Disabled, 1b = Enabled */
#define MCR_WARN_INT        (1UL << 21) /* Warning Interrupt Enable -- Enables generation of errors in status register - 0b - Disabled, 1b = Enabled */
#define MCR_LOW_POWER_ACK   (1UL << 20) /* Low-Power Mode Acknowledge -- (Read-only) Indicates FlexCAN is in low-power mode - 0b = Not in mode, 1b = in mode */
#define MCR_WAKE_SOURCE     (1UL << 19) /* Wake Up Source -- Whether low-pass filter applied to Rx - 0b = unfiltered, 1b = filtered */
#define MCR_DOZE            (1UL << 18) /* Doze Mode Enable -- Determines whether can go low-power when Doze requested - 0b = Disabled, 1b = Enabled */
#define MCR_SELF_RECEPTION  (1UL << 17) /* Self Reception Disable -- Whether FlexCAN receive frames transmitted by itself - 0b = Enabled, 1b = Disabled */
#define MCR_RX_MASK_QUEUE   (1UL << 16) /* Individual Rx Masking and Queue Enable -- Determines matching scheme for Rx - 0b = Disabled, 1b = Enabled */
#define MCR_DMA             (1UL << 15) /* DMA - Enable -- Controls whether DMA is enabled or not for Rx FIFO - 0b = Disabled, 1b = Enabled */
#define MCR_RESERVED_0      (1UL << 14) /* Reserved */
#define MCR_LOCAL_PRIORITY  (1UL << 13) /* Local Priority Enable -- Local priority control for backward compatibility - 0b = Disabled, 1b = Enabled */
#define MCR_ABORT           (1UL << 12) /* Abort Enable -- Enables Tx abort mechanism - 0b = Disabled, 1b = Enabled */
#define MCR_CAN_FD          (1UL << 11) /* CAN FD Operation Enable -- Enables CANFD operation - 0b = Disabled, 1b = Enabled */
#define MCR_RESERVED_1      (1UL << 10) /* Reserved */
#define MCR_ID_ACCEPT       (3UL << 8) /* ID Acceptance Mode - 2-bit field identifies format of Rx FIFO ID filter table elements - See docs for details*/
#define MCR_RESERVED_2      (1UL << 7) /* Reserved */
#define MCR_NUM_MB          (127UL << 0) /* Number Of The Last Message Buffer - 7-bit field defines number of last message buffers - See docs for details */


/* Can break these up into separate structs for different groupings of registers */
/* Use reserved to pad out when there is a gap in the hex (the gap might be as other devices might use them but we don't)*/

/* TODO - ATM these are organised as separate structs but really they're just offsets into memory -- should combine them into a megastruct as 
the DTB treats them as a single region. Talk to Ivan about easiest/neatest way to do this */

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
}

/* FlexCAN Receive Mask Registers - these are used to specify IDs to filter for when receiving CAN messages */
// TODO - atm these are just left out but from 880-97C are 64, 32-bit Rx Individual Mask Registers

/* FlexCAN Error Registers - these are for reading error occurrences */
struct error_registers {
    uint32_t mecr;          /* AE0h Memory Error Control Register */
    uint32_t erriar;        /* AE4h Error Injection Address Register */
    uint32_t erridpr;       /* AE8h Error Injection Data Pattern Register */
    uint32_t errippr;       /* AECh Error Injection Parity Pattern Register */
    uint32_t rerrar;        /* AF0h Error Report Address Register */
    uint32_t rerrdr;        /* AF4h Error Report Data Register */
    uint32_t rerrsynr;      /* AF8h Error Report Syndrome Register */
    uint32_t errsr;         /* AFCh Error Status Register */
}

/* FlexCAN CANFD Registers - these are for enabling and using CANFD */
struct canfd_registers {
    uint32_t fdctrl;        /* C00h CAN FD Control Register */
    uint32_t fdcbt;         /* C04h CAN FD Bit Timing Register */
    uint32_t fdcrc;         /* C08h CAN FD CRC Register */
}