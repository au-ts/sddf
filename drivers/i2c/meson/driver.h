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
#include <stdbool.h>
#include <sddf/util/printf.h>
#include <sddf/i2c/queue.h>
#include "gpio.h"
#include "clk.h"

// Driver "state". Referred to as "data" to avoid confusion with the finite state machine.
// This contains data that must persist BETWEEN states.
typedef struct i2c_driver_data {
    /* Pointer to current request/response being handled */
    i2c_cmd_t *curr_data;
    /* Pointer to base of current meta region */
    uintptr_t meta_base;
    /* Number of cmds in current request */
    int curr_request_len;
    /* Index into current request. */
    unsigned int req_idx;
    /* Current command. Aliased from `curr_data`/`req_idx` for structural reasons*/
    i2c_cmd_t *active_cmd;
    /* Number of read/write ops successfully dispatched, used to track working in S_CMD */
    uint8_t rw_idx;
    /* Number of bytes received back from hardware, used to track when a read request is done*/
    uint8_t bytes_read;
    /* I2C bus address of the current request being handled */
    i2c_addr_t addr;
    /* Is this cmd pending a start, address, subaddress (preceding read) or stop token? */
    bool await_start, await_addr, await_stop;   // Flags for single-token ops
    uint8_t await_wrrd;     // Countdown of steps for the wrrd op. 0 = nothing to do.
                            // This is needed to prevent requiring two full commands
                            // to write to a device subaddress! Steps:
                            // Write WRITE, write ADDR, READ dev addr, continue as normal
    i2c_err_t err;

} i2c_driver_data_t;

// I2C FSM. We add NUM_STATES to the end of the enum as a hack to get the length.
typedef enum { S_IDLE, S_REQ, S_SEL_CMD, S_CMD, S_CMD_RET, S_RESPONSE, NUM_STATES } i2c_state_t;

// FSM data ... what's running, what's next.
typedef struct fsm {
    i2c_state_t curr_state;
    i2c_state_t next_state;
    bool yield; // fsm funcs can set this to tell the FSM loop to allow the PD to sleep
} fsm_data_t;

// Each state implements a single state function which is called by the FSM.
typedef void i2c_state_func_t(fsm_data_t *fsm, i2c_driver_data_t *data);

// Prototype for FSM function
void fsm(fsm_data_t *f);

static void i2c_reset_state(i2c_driver_data_t *s)
{
    s->curr_data = NULL;
    s->meta_base = 0;
    s->curr_request_len = 0;
    s->req_idx = 0;
    s->rw_idx = 0;
    s->bytes_read = 0;
    s->addr = 0;
    s->active_cmd = NULL;
    s->await_start = false;
    s->await_addr = false;
    s->await_stop = false;
    s->await_wrrd = 0;
    s->err = I2C_ERR_OK;
}

#define NUM_WRRD_STEPS 3    // Address, subaddress, START

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
