/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <sddf/util/printf.h>
#include <sddf/i2c/queue.h>

// (i2c) driver.h
// Header containing all generic features for I2C drivers targeting the
// sDDF and Microkit platform.
// Lesley Rossouw (lesley.rossouw@unsw.edu.au)
// 08/2025
//
#pragma once

// Driver "state". Referred to as "data" to avoid confusion with the finite state machine.
// This contains data that must persist BETWEEN states.
typedef struct i2c_driver_data {
    /* Pointer to head of current request */
    i2c_cmd_t curr_request;
    /* Index into current request. I.e. number of commands popped. */
    unsigned int req_idx;
    /* Current command. Aliased from `curr_data`/`req_idx` for structural reasons*/
    i2c_cmd_t active_cmd;
    /* Number of read/write ops successfully dispatched, used to track working in S_CMD */
    uint8_t rw_idx;
    /* Number of bytes received back from hardware, used to track when a read request is done*/
    uint8_t bytes_read;
    /* Is current cmd pending a start, address, subaddress (preceding read) or stop token? */
    bool await_start, await_addr, await_stop;
    /* Countdown of steps for the wrrd op. 0 = nothing to do.
     * This is needed to prevent requiring two full commands
     * to write to a device subaddress! Steps:
     * Write WRITE, write ADDR, READ dev addr, continue as normal
     */
    uint8_t await_wrrd;
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
    memset(s, 0, sizeof(i2c_driver_data_t));
}

static inline uint8_t i2c_curr_req_len(i2c_driver_data_t *s)
{
    return s->curr_request.payload.i2c_header.batch_len;
}

static inline i2c_addr_t i2c_curr_addr(i2c_driver_data_t *s)
{
    return s->curr_request.payload.i2c_header.address;
}

#define NUM_WRRD_STEPS  3   // 3 statees to do a write-read
#define WRRD_WRADDR     3   // Address (write)
#define WRRD_SUBADDR    2   // Send register address
#define WRRD_RDADDR     1   // Address (read) (implicit)
