/*
 * Copyright 2026, Skykraft
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/i2c/config.h>

/*
 * I2C header for the Zynq UltraScale+ MPSoCs
 * Zynq UltraScale+ Device Technical Reference Manual (UG1085)
 * https://docs.amd.com/v/u/en-US/ug1085-zynq-ultrascale-trm
 * 
 * The I2C device is documented in Chapter 22 
*/

/* Register definitions for Zynq Ultrascale
 * Zynq UltraScale+ Devices Register Reference (UG1087)
 * https://docs.amd.com/r/en-US/ug1087-zynq-ultrascale-registers/I2C-Module
 */
typedef struct zynq_i2c_regs {
    uint32_t ctrl;          /* 0x0 - Control reg */
    uint32_t status;        /* 0x4 - Status reg */     
    uint32_t i2c_addr;      /* 0x8 - I2C address reg */
    uint32_t i2c_data;      /* 0xc - I2C data reg */
    uint32_t isr;           /* 0x10 - Interrupt status reg */
    uint32_t tf_size;       /* 0x14 - Transfer size reg */
    uint32_t slave_mon;     /* 0x18 - Slave monitor pause reg */
    uint32_t sclk_to;       /* 0x1c - SCLK (I/O) timeout reg */
    uint32_t imr;           /* 0x20 - Interrupt mask reg */
    uint32_t ier;           /* 0x24 - Interrupt enable reg */
    uint32_t idr;           /* 0x28 - Interrupt disable reg */
    uint32_t gfr;           /* 0x2c - Glitch filter reg */
} zynq_i2c_regs_t;

/* Hardware Parameters */
#define ZYNQ_FIFO_DEPTH 16
#define ZYNQ_MAX_TF_SIZE ((uint32_t)(255 - 3))
/**
 * This is the default LPD_LSBUS_CLK on ZynqMP Ultrascale+,
 * but if you have modified it, you *must* update this  
 */
#define ZYNQ_LPD_LSBUS_CLK 100000000    /* Zynq input clock (100MHz) */
#define ZYNQ_I2C_SCLK_FREQ 400000       /* SCLK Frequency (Hz) */

/* Interrupts */
#define INT_ALL_MASK        (0x2FF)    /* All interrupts */
#define INT_ARB_LOST_MASK   BIT(9)     /* Arbitration lost */
#define INT_RX_UNF_MASK     BIT(7)     /* FIFO receive underflow */
#define INT_TX_OVF_MASK     BIT(6)     /* FIFO transmit overflow */
#define INT_RX_OVF_MASK     BIT(5)     /* Receive overflow */
#define INT_SLV_RDY_MASK    BIT(4)     /* Monitored slave ready */
#define INT_TO_MASK         BIT(3)     /* Transfer time out */
#define INT_NACK_MASK       BIT(2)     /* Transfer not acknowledged */
#define INT_DATA_MASK       BIT(1)     /* More data */
#define INT_COMP_MASK       BIT(0)     /* Transfer complete */

/* I2C control properties */
#define I2C_CTRL_RESET_MASK         (0x0000)
#define I2C_CTRL_RESET_CONFIG_MASK  (0x40)
#define I2C_CTRL_CLEAR_MASK         (~(0x0015) | 0x0040)
#define I2C_CTRL_MASTER_INIT_MASK   (0x5E)
#define I2C_CTRL_CLR_FIFO           BIT(6)
#define I2C_CTRL_SLVMON             BIT(5)
#define I2C_CTRL_HOLD               BIT(4)
#define I2C_CTRL_ACK_EN             BIT(3)
#define I2C_CTRL_NA_MODE            BIT(2) /* Normal addressing (7-bit) */
#define I2C_CTRL_MASTER_MODE        BIT(1)
#define I2C_CTRL_MASTER_RX_EN       BIT(0)
#define I2C_CTRL_MASTER_TX_EN       (~I2C_CTRL_MASTER_RX_EN)
#define I2C_CTRL_NOT_RW_MASK        (0xFFFE)
#define I2C_CTRL_CLR_DIV_MASK       (0x00FF)
#define I2C_CTRL_DIV_A_MAX          (0x3)
#define I2C_CTRL_DIV_B_MAX          (0x3F)
#define I2C_CTRL_DIV_A_OFFSET       (14)
#define I2C_CTRL_DIV_B_OFFSET       (8)

/* I2C status properties */
#define I2C_STAT_RXDV       BIT(5)
#define I2C_STAT_BUS_ACTIVE BIT(8)

/* I2C glitch filter properties */
#define I2C_GFR_RESET_VAL 0x5

/* I2C timeout properties */
// TRM states 0xFF as reset value, while register manual states 0x1F.
// #define I2C_TO_RESET_MASK       (0xFF)
#define I2C_TO_RESET_MASK       (0x1F)

/* I2c transfer size properties */
#define I2C_TF_SIZE_RESET_MASK  (0x00)