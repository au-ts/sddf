/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/i2c/i2c_driver.h>
#include <sddf/i2c/config.h>

// Define in your i2c.c
extern i2c_driver_config_t config;
extern i2c_driver_data_t driver_data;
extern fsm_data_t fsm_data;
extern i2c_queue_handle_t queue_handle;
extern i2c_state_func_t *i2c_state_table[NUM_STATES];

// For 99% of cases, the following state definition will be correct for your driver.
// Only replace this in your implementation if you need to add new states, otherwise
// just copy and paste this.

// i2c_state_func_t *i2c_state_table[NUM_STATES] = { state_idle, state_req,     state_sel_cmd,
//                                                   state_cmd,  state_cmd_ret, state_resp };

/**
 * I2C finite state machine. Abstracts stateful execution into fixed states to improve
 * maintainability (and save a little bit of room on the stack!). The FSM responds
 * to *internal* events principally, not Microkit events. As a result, we depend upon
 * state functions to declare when the PD should go to sleep by setting yield to true.
 */
void fsm(fsm_data_t *f)
{
    do {
        LOG_I2C_DRIVER("FSM: %s\n", state_to_str(f->curr_state));
        // Run current state
        i2c_state_table[f->curr_state](&fsm_data, &driver_data, &queue_handle);
        f->curr_state = f->next_state;
        LOG_I2C_DRIVER("Next state: %s\n", state_to_str(f->next_state));
    } while (!f->yield);
    // Always reset the yield flag when the FSM gives up. Whenever this function
    // returns the PD should have gone to sleep.
    f->yield = false;
    LOG_I2C_DRIVER("FSM: yielding in state = %s\n", state_to_str(f->curr_state));
}

/**
 * This function handles the hardware finishing working on a command.
 * This should ideally be called after an IRQ arrives to wake the driver
 * after the driver dispatched some work.
 */
void fsm_cmd_done(fsm_data_t *fsm_data)
{
    if (fsm_data->curr_state == S_CMD_RET) {
        fsm(fsm_data);
    } else {
        LOG_I2C_DRIVER_ERR("Received spurious completion interrupt!\n");
    }
}

/**
 * This function handles notifications from the virtualiser, either
 * launching into the idle state to begin work or ignoring the notification
 * because the driver is already running.
 * This should be called in response to virtualiser notifications.
 */
void fsm_virt_notified(fsm_data_t *fsm_data)
{
    if (fsm_data->curr_state == S_IDLE)
        fsm(fsm_data);
}

/**
 * S_IDLE
 * Reset driver data and goto request state if there's work to do. Otherwise, go to sleep.
 *
 * Succeeds: S_RESP, or any state when failing
 * Sucessor(s): S_REQ
 */
void state_idle(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    LOG_I2C_DRIVER("S_IDLE\n");
    i2c_reset_state(data);
    if (!i2c_queue_empty(queue_handle->request->ctrl)) {
        // There's a request to handle!
        fsm->next_state = S_REQ;
    } else {
        // No work to do, go to sleep.
        fsm->yield = true;
    }
    return;
}

/**
 * S_REQ (request stated)
 * Take a new request from the queue and set up internal driver state (driver_data)
 *
 * Succeeds: S_IDLE
 * Successor(s): S_SEL_CMD (success), S_IDLE (fail)
 */
void state_req(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    LOG_I2C_DRIVER("S_REQ\n");
    // Pre-emptively set S_IDLE as next state in case any of the error checks fail.
    // If we fail in this state, something has gone *horribly* wrong because the virt
    // checks all relevant fields first!
    fsm->next_state = S_IDLE;

    // Sanity check. This should be impossible.
    if (i2c_queue_empty(queue_handle->request->ctrl)) {
        LOG_I2C_DRIVER_ERR("State machine reached invalid state! In request state without work to do...");
        assert(false);
    }

    // Get request from queue
    // Otherwise, begin work. Start by extracting the request.
    // Throw away non-header requests in case the previous request failed.
    i2c_cmd_t header;
    int err;
    do {
        if (i2c_queue_empty(queue_handle->request->ctrl)) {
            // No more work, we were just left to clean up data.
            fsm->next_state = S_IDLE;
            return;
        }
        err = i2c_dequeue_request(*queue_handle, &header);
    } while (!(header.flag_mask & I2C_FLAG_HEAD));

    // If this fails, the virt is broken.
    assert(header.flag_mask & I2C_FLAG_HEAD);
    if (err) {
        LOG_I2C_DRIVER_ERR("fatal: failed to dequeue request\n");
        return;
    }
    if (header.payload.i2c_header.batch_len > I2C_MAX_DATA_SIZE
        || header.payload.i2c_header.batch_len > i2c_queue_length((queue_handle->request)->ctrl)) {
        LOG_I2C_DRIVER_ERR("Incoherent request size! %u!\n", header.payload.i2c_header.batch_len);
        assert(false); // Virt is broken.
    }
    LOG_I2C_DRIVER("Loading request for bus address 0x%x\n", header.payload.i2c_header.address);

    memcpy(&(data->curr_request), &header, sizeof(i2c_cmd_t));
    data->err = I2C_ERR_OK;
    fsm->next_state = S_SEL_CMD;
    return;
}

/**
 * S_SEL_CMD (command)
 * Select a new subcommand of the current request to work on.
 * This sets up the await flags and rw_idx, as well as keeping track of progression through
 * the buffer. It also decides when the request is finished.
 * Succeeds: S_REQ, S_CMD_RET
 * Sucessor(s): S_CMD, S_IDLE (fatal), S_RESPONSE (done or error)
 */
void state_sel_cmd(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    LOG_I2C_DRIVER("S_SEL_CMD\n");
    // If we're in this state, we know that either:
    // a. There's no active command (just started)
    // b. The previous command finished.
    // We must decide on the next command, or retire to S_RESP

    // Get next command
    if (data->req_idx < i2c_curr_req_len(data)) {
        LOG_I2C_DRIVER("Accepting new cmd...\n");
        i2c_cmd_t cmd;
        int err = i2c_dequeue_request(*queue_handle, &cmd);
        assert(!err);

        // Invariant: we never encounter an unexpected header. The virt should
        // ensure this.
        assert(!(cmd.flag_mask & I2C_FLAG_HEAD));

        // Set interface state
        data->await_start = true;    // We can never skip starting!
        // Don't send address if this is a repeat start
        data->await_addr = !(cmd.flag_mask & I2C_FLAG_RSTART);

        // Set write-read counter if needed. Tracks operations (send start, addr, read)
        data->await_wrrd = (cmd.flag_mask & I2C_FLAG_WRRD) ? NUM_WRRD_STEPS : 0;
        data->await_stop = cmd.flag_mask & I2C_FLAG_STOP;
        data->rw_idx = 0;
        data->active_cmd = cmd;

        LOG_I2C_DRIVER("## Command loaded (SEL_CMD) ##\n");
        LOG_I2C_DRIVER("\t len = %u\n", cmd.data_len);
        // A write-read always needs to read.
        LOG_I2C_DRIVER("\t FLAG_READ: %u\n", (cmd.flag_mask & (I2C_FLAG_READ | I2C_FLAG_WRRD)) != 0);
        LOG_I2C_DRIVER("\t FLAG_WRRD: %u\n", (cmd.flag_mask & I2C_FLAG_WRRD) != 0);
        LOG_I2C_DRIVER("\t FLAG_STOP: %u\n", (cmd.flag_mask & I2C_FLAG_STOP) != 0);
        LOG_I2C_DRIVER("\t FLAG_RSTART: %u\n", (cmd.flag_mask & I2C_FLAG_RSTART) != 0);

        // Increment req idx for next time
        data->req_idx++;
        if (data->req_idx == i2c_curr_req_len(data) - 1) {
            LOG_I2C_DRIVER("Handling last cmd of request...\n");
        }
        fsm->next_state = S_CMD;
    } else {
        LOG_I2C_DRIVER("Request finished!\n");
        fsm->next_state = S_RESPONSE;
    }
    return;
}

/**
 * S_RESP
 * Handle returning current request to virt.
 *
 * Succeeds: S_SEL_CMD (success), any other state (err set)
 * Sucessor(s): S_IDLE
 */
void state_resp(fsm_data_t *f, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    LOG_I2C_DRIVER("S_RESP\n");
    if (i2c_queue_full(queue_handle->response->ctrl)) {
        LOG_I2C_DRIVER_ERR("Tried to return a response, but no buffers are available! Dropping..\n");
        f->next_state = S_IDLE;
        i2c_halt();
        return;
    }

    // Handle failure
    int ret;
    i2c_addr_t address = i2c_curr_addr(data);
    if (data->err) {
        LOG_I2C_DRIVER("Request failed with error %s\n", i2c_err_to_str(data->err));
        ret = i2c_enqueue_response(*queue_handle, address, data->err, data->req_idx);
        i2c_halt();
    } else {
        LOG_I2C_DRIVER("Request returning with no error: address = %u, bytes_read = %u\n", address, data->bytes_read);
        ret = i2c_enqueue_response(*queue_handle, address, data->err, 0);
    }
    if (ret) {
        LOG_I2C_DRIVER_ERR("Failed to return response to virt!\n");
    }
    f->next_state = S_IDLE;
    microkit_notify(config.virt.id);
}
