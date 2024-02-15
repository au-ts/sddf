/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// i2c-driver.h
// Header containing all generic features for I2C drivers targeting the
// sDDF and seL4 core platform.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#ifndef I2C_DRIVER_H
#define I2C_DRIVER_H

#include <stdint.h>
#include <sddf/util/printf.h>
#include <sddf/util/fence.h>
#include "transport.h"
#include "gpio.h"
#include "clk.h"

#define TOKEN_LIST_MAX 128
#define WBUF_SZ_MAX 64
#define RBUF_SZ_MAX 64

// Driver state
typedef struct _i2c_ifState {
    req_buf_ptr_t current_req; // Pointer to current request.
    ret_buf_ptr_t current_ret; // Pointer to current return buf.
    int current_ret_len;        // Number of bytes in current return.
    int current_req_len;        // Number of bytes in current request.
    size_t remaining;              // Number of bytes remaining to dispatch.
    int notified;               // Flag indicating that there is more work waiting.
    int data_direction;                    // Data direction. 0 = write, 1 = read.
} i2c_ifState_t;

#define DATA_DIRECTION_WRITE (0x0)
#define DATA_DIRECTION_READ (0x1)

// I2C registers are indexed as their memory region + 4*offset.
// Unless otherwise indicated, all fields are two words long.
#define I2C_CTRL        (0x0)         // One word
#define I2C_ADDRESS     (0x1)         // One word
#define I2C_TOKEN_LIST  (0x2)
#define I2C_WDATA       (0x4)
#define I2C_RDATA       (0x6)

// Ctl register fields
#define REG_CTRL_START      (BIT(0))
#define REG_CTRL_ACK_IGNORE (BIT(1))
#define REG_CTRL_STATUS     (BIT(2))
#define REG_CTRL_ERROR      (BIT(3))
#define REG_CTRL_CURR_TK    (BIT(4) | BIT(5) | BIT(6) | BIT(7))
#define REG_CTRL_RD_CNT     (BIT(8) | BIT(9) | BIT(10) | BIT(11))
#define REG_CTRL_MANUAL     (BIT(22))
#define REG_CTRL_MAN_S_SCL  (BIT(23))
#define REG_CTRL_MAN_S_SDA  (BIT(24))
#define REG_CTRL_MAN_G_SCL  (BIT(25))
#define REG_CTRL_MAN_G_SDA  (BIT(26))
#define REG_CTRL_CNTL_JIC   (BIT(31))
#define REG_CTRL_CLKDIV_SHIFT   (12)
#define REG_CTRL_CLKDIV_MASK    ((BIT(10) - 1) << REG_CTRL_CLKDIV_SHIFT)

// Addr register fields
#define REG_ADDR_SCLDELAY_SHFT      (16)
#define REG_ADDR_SDAFILTER          (BIT(8) | BIT(9) | BIT(10))
#define REG_ADDR_SCLFILTER          (BIT(11) | BIT(12) | BIT(13))
#define REG_ADDR_SCLDELAY_ENABLE    (BIT(28))

#define MESON_I2C_TK_END      (0x0)   // END: Terminator for token list, has no meaning to hardware otherwise
#define MESON_I2C_TK_START    (0x1)   // START: Begin an i2c transfer. Causes master device to capture bus.
#define MESON_I2C_TK_ADDRW    (0x2)   // ADDRESS WRITE: Used to wake up the target device on the bus. Sets up
                                    //                any following DATA tokens to be writes.
#define MESON_I2C_TK_ADDRR    (0x3)   // ADDRESS READ: Same as ADDRW but sets up DATA tokens as reads.
#define MESON_I2C_TK_DATA     (0x4)   // DATA: Causes hardware to either read or write a byte to/from the read/write buffers.
#define MESON_I2C_TK_DATA_END (0x5)   // DATA_LAST: Used for read transactions to write a NACK to alert the slave device
                                    //            that the read is now over.
#define MESON_I2C_TK_STOP     (0x6)   // STOP: Used to send the STOP condition on the bus to end a transaction. 
                                    //       Causes master to release the bus.

// Driver-server interface
#include "i2c-token.h"
#define SERVER_NOTIFY_ID 1


#endif
