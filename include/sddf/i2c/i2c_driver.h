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

/*
 *  This file defines a state machine that implements most of
 *  the i2c driver. Users must implement the following:
 *
 *  i2c_halt()  -- tell hardware to throw away any state
 *  state_cmd()     -- load data into hardware and start working
 *  state_cmd_ret() -- extract returned data from hardware
 *
 */

#pragma once

// #define DEBUG_I2C_DRIVER
#ifdef DEBUG_I2C_DRIVER
#define LOG_I2C_DRIVER(...) do{ sddf_dprintf("I2C DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_I2C_DRIVER(...) do{}while(0)
#endif

#define LOG_I2C_DRIVER_ERR(...) do{ sddf_dprintf("I2C DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

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
typedef void i2c_state_func_t(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle);

// Prototype for FSM function
void fsm(fsm_data_t *f);

// Utility functions for driver
/**
 * Return TRUE if current command is a read operation, irrespective of WRRD ops.
 */
static bool cmd_is_read(i2c_cmd_t c)
{
    return c.flag_mask & I2C_FLAG_READ;
}

/**
 * Return TRUE if current token corresponds to a read, else FALSE.
 * This function exists to handle correctly sending the WRRD write.
 */
static bool data_direction_rd(i2c_driver_data_t *data)
{
    return cmd_is_read(data->active_cmd) & !data->await_wrrd;
}

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

// ### FSM utility function prototypes ###

/**
 *  Stop the hardware from operating and return to a state where S_REQ can
 *  resume.
 */
int i2c_halt(void);

/**
 * This function handles the hardware finishing working on a command.
 * This should ideally be called after an IRQ arrives to wake the driver
 * after the driver dispatched some work.
 */
void fsm_cmd_done(fsm_data_t *fsm_data);

/**
 * This function handles notifications from the virtualiser, either
 * launching into the idle state to begin work or ignoring the notification
 * because the driver is already running.
 * This should be called in response to virtualiser notifications.
 */
void fsm_virt_notified(fsm_data_t *fsm_data);

// I2C state machine states

// Implement these for your driver - use meson driver as a template if needed.
/**
 * S_CMD (command)
 * Initiate work for the current command then go to S_CMD_RET to await device completion.
 * Succeeds: S_SEL_CMD, S_CMD_RET
 * Sucessor(s): S_CMD_RET, S_RESPONSE (error)
 */
void state_cmd(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle);

/**
 * S_CMD_RET
 * Handle return of data from hardware after S_CMD goes to sleep post-load. Decides whether to
 * continue working on the current command or to return to S_SEL_CMD for a new one.
 *
 * Succeeds: S_CMD
 * Sucessor(s): S_CMD (cmd not finished yet), S_SEL_CMD (cmd finished), S_RESP (error)
 */
void state_cmd_ret(fsm_data_t *f, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle);

// These states should be usable unchanged for 99% of i2c peripherals.
// only replace these if absolutely necessary. Default implementations
// are in sddf/drivers/i2c/i2c_common.c

/**
 * S_IDLE
 * Reset driver data and goto request state if there's work to do. Otherwise, go to sleep.
 *
 * Succeeds: S_RESP, or any state when failing
 * Sucessor(s): S_REQ
 */
void state_idle(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle);

/**
 * S_REQ (request stated)
 * Take a new request from the queue and set up internal driver state (driver_data)
 *
 * Succeeds: S_IDLE
 * Successor(s): S_SEL_CMD (success), S_IDLE (fail)
 */
void state_req(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle);

/**
 * S_SEL_CMD (command)
 * Select a new subcommand of the current request to work on.
 * This sets up the await flags and rw_idx, as well as keeping track of progression through
 * the buffer. It also decides when the request is finished.
 * Succeeds: S_REQ, S_CMD_RET
 * Sucessor(s): S_CMD, S_IDLE (fatal), S_RESPONSE (done or error)
 */
void state_sel_cmd(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle);

/**
 * S_RESP
 * Handle returning current request to virt.
 *
 * Succeeds: S_SEL_CMD (success), any other state (err set)
 * Sucessor(s): S_IDLE
 */
void state_resp(fsm_data_t *f, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle);



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
        return "S_OTHER";
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

#define NUM_WRRD_STEPS  3   // 3 statees to do a write-read
#define WRRD_WRADDR     3   // Address (write)
#define WRRD_SUBADDR    2   // Send register address
#define WRRD_RDADDR     1   // Address (read) (implicit)
