/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/i2c/i2c_driver.h>
#include "gpio.h"
#include "clk.h"
#pragma once

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

// Constants for token register handling
#define I2C_MAX_TK_OFFSET   (16)
#define I2C_MAX_WDATA       (8)
#define I2C_MAX_RDATA       (8)

/* The client cannot attach or use a bus address greater than 7-bits. */
#define MESON_I2C_MAX_BUS_ADDRESS (0x7f)

const char *meson_token_to_str(uint8_t token)
{
    switch (token) {
    case MESON_I2C_TOKEN_END:
        return "MESON_I2C_TOKEN_END";
    case MESON_I2C_TOKEN_START:
        return "MESON_I2C_TOKEN_START";
    case MESON_I2C_TOKEN_ADDR_WRITE:
        return "MESON_I2C_TOKEN_ADDR_WRITE";
    case MESON_I2C_TOKEN_ADDR_READ:
        return "MESON_I2C_TOKEN_ADDR_READ";
    case MESON_I2C_TOKEN_DATA:
        return "MESON_I2C_TOKEN_DATA";
    case MESON_I2C_TOKEN_DATA_END:
        return "MESON_I2C_TOKEN_DATA_END";
    case MESON_I2C_TOKEN_STOP:
        return "MESON_I2C_TOKEN_STOP";
    default:
        return "Unknown token!";
    }
}

static inline const char *state_to_str(i2c_state_t s)
{
    switch (s) {
    case S_IDLE:
        return "S_IDLE";
    case S_REQ:
        return "S_REQ";
    case S_SEL_CMD:
        return "S_SEL_CMD";
    case S_CMD:
        return "S_CMD";
    case S_CMD_RET:
        return "S_CMD_RET";
    case S_RESPONSE:
        return "S_RESPONSE";
    default:
        return "S_INVALID!";
    }
}

static inline const char *i2c_err_to_str(i2c_err_t err)
{
    switch (err) {
    case I2C_ERR_OK:
        return "I2C_ERR_OK";
    case I2C_ERR_TIMEOUT:
        return "I2C_ERR_TIMEOUT";
    case I2C_ERR_NACK:
        return "I2C_ERR_NACK";
    case I2C_ERR_NOREAD:
        return "I2C_ERR_NOREAD";
    case I2C_ERR_BADSEQ:
        return "I2C_ERR_BADSEQ";
    case I2C_ERR_OTHER:
        return "I2C_ERR_OTHER";
    default:
        return "Invalid error";
    }
}
