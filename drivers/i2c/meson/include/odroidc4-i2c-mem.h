/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// i2c-mem.h
// Abstracts away device memory mappings for DMA for the ODROID C4.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

// Note that the entire I2C memory region fits in one 2MiB page
// originating at I2C_BASE, which is page aligned.

#ifndef I2C_MEM_H
#define I2C_MEM_H
#define BIT(n)  (1U << (n))

// I2C registers are indexed as their memory region + 4*offset.
// Unless otherwise indicated, all fields are two words long.
#define I2C_CTRL        (0x0)         // One word
#define I2C_ADDRESS     (0x1)         // One word
#define I2C_TOKEN_LIST  (0x2)
#define I2C_WDATA       (0x4)
#define I2C_RDATA       (0x6)

// Ctl register fields
#define REG_CTRL_START		(BIT(0))
#define REG_CTRL_ACK_IGNORE	(BIT(1))
#define REG_CTRL_STATUS		(BIT(2))
#define REG_CTRL_ERROR		(BIT(3))
#define REG_CTRL_CURR_TK    (BIT(4) | BIT(5) | BIT(6) | BIT(7))
#define REG_CTRL_RD_CNT     (BIT(8) | BIT(9) | BIT(10) | BIT(11))
#define REG_CTRL_MANUAL     (BIT(22))
#define REG_CTRL_MAN_S_SCL  (BIT(23))
#define REG_CTRL_MAN_S_SDA  (BIT(24))
#define REG_CTRL_MAN_G_SCL  (BIT(25))
#define REG_CTRL_MAN_G_SDA  (BIT(26))
#define REG_CTRL_CNTL_JIC   (BIT(31))
#define REG_CTRL_CLKDIV_SHIFT	(12)
#define REG_CTRL_CLKDIV_MASK	((BIT(10) - 1) << REG_CTRL_CLKDIV_SHIFT)

// Addr register fields
#define REG_ADDR_SCLDELAY_SHFT      (16)
#define REG_ADDR_SDAFILTER          (BIT(8) | BIT(9) | BIT(10))
#define REG_ADDR_SCLFILTER          (BIT(11) | BIT(12) | BIT(13))
#define REG_ADDR_SCLDELAY_ENABLE    (BIT(28))

#define OC4_I2C_TK_END      (0x0)   // END: Terminator for token list, has no meaning to hardware otherwise
#define OC4_I2C_TK_START    (0x1)   // START: Begin an i2c transfer. Causes master device to capture bus.
#define OC4_I2C_TK_ADDRW    (0x2)   // ADDRESS WRITE: Used to wake up the target device on the bus. Sets up
                                    //                any following DATA tokens to be writes.
#define OC4_I2C_TK_ADDRR    (0x3)   // ADDRESS READ: Same as ADDRW but sets up DATA tokens as reads.
#define OC4_I2C_TK_DATA     (0x4)   // DATA: Causes hardware to either read or write a byte to/from the read/write buffers.
#define OC4_I2C_TK_DATA_END (0x5)   // DATA_LAST: Used for read transactions to write a NACK to alert the slave device
                                    //            that the read is now over.
#define OC4_I2C_TK_STOP     (0x6)   // STOP: Used to send the STOP condition on the bus to end a transaction. 
                                    //       Causes master to release the bus.

// IRQs IDs (matching i2c.system)
#define IRQ_I2C          2
#define IRQ_I2C_TO       3

#endif
