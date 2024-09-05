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

#pragma once

#include <stdint.h>
#include <sddf/util/printf.h>
#include "gpio.h"
#include "clk.h"

#define DATA_REGIONS_START 0x10000000

enum data_direction {
    DATA_DIRECTION_WRITE = 0x0,
    DATA_DIRECTION_READ = 0x1
};

// Driver state
typedef struct _i2c_ifState {
    /* Pointer to current request/response being handled */
    uint8_t *curr_data;
    /* Number of bytes in current request (number of tokens) */
    int curr_request_len;
    /* Number of bytes in current response (only the data) and not the error tokens at the start */
    int curr_response_len;
    /* Number of bytes remaining to dispatch in the current request.*/
    size_t remaining;
    /* Flag indicating that there is more independent requests waiting on the queue_handle.request. */
    bool notified;

    /* Number of bytes to read/write if request data offset is in the midst of a buffer. If this is
       zero, no read/write is in progress and we can interpret the current byte as a token.*/
    uint8_t rw_remaining;

    enum data_direction data_direction;
    /* I2C bus address of the current request being handled */
    size_t addr;
} i2c_ifState_t;

#define DATA_DIRECTION_WRITE (0x0)
#define DATA_DIRECTION_READ (0x1)

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

#define MESON_I2C_TOKEN_END      (0x0)          // END: Terminator for token list, has no meaning to hardware otherwise
#define MESON_I2C_TOKEN_START    (0x1)          // START: Begin an i2c transfer. Causes master device to capture bus.
#define MESON_I2C_TOKEN_ADDR_WRITE    (0x2)     // ADDRESS WRITE: Used to wake up the target device on the bus. Sets up
// any following DATA tokens to be writes.
#define MESON_I2C_TOKEN_ADDR_READ    (0x3)      // ADDRESS READ: Same as ADDRW but sets up DATA tokens as reads.
#define MESON_I2C_TOKEN_DATA     (0x4)          // DATA: Causes hardware to either read or write a byte to/from the read/write buffers.
#define MESON_I2C_TOKEN_DATA_END (0x5)          // DATA_LAST: Used to indicate the last 8-bit byte transfer is a byte transfer of a READ
#define MESON_I2C_TOKEN_STOP     (0x6)          // STOP: Used to send the STOP condition on the bus to end a transaction.
// Causes master to release the bus.

/* The client cannot attach or use a bus address greater than 7-bits. */
#define MESON_I2C_MAX_BUS_ADDRESS (0x7f)
