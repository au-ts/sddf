/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Implementation of the i2c driver targeting the ODROID C4.
// Each instance of this driver corresponds to one of the four
// available i2c master interfaces on the device.
// Lesley Rossouw (lesley.rossouw@unsw.edu.au)
// 05/2025

#include <microkit.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/config.h>
#include <sddf/resources/device.h>
#include <string.h>
#include "driver.h"

#ifndef I2C_BUS_NUM
#error "I2C_BUS_NUM must be defined!"
#endif

// Uncomment to enable logging
// #define DEBUG_I2C_DRIVER

// Note that only the first 16 bits are used in these fields
// The last 16 bits in each field is for padding
struct i2c_regs {
    uint32_t addr;          // slave address and other fields      
    uint32_t freq;          
    uint32_t ctl;           // control register
    uint32_t status;
    uint32_t data;
}

// TODO: check how to configure this
__attribute__((__section__(".i2c_driver_config"))) i2c_driver_config_t config;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

// TODO: check what these should be on imx
// Hardware memory
uintptr_t clk_regs = 0x30000000;
uintptr_t gpio_regs = 0x30100000;

volatile struct i2c_regs *regs;

// Driver state for each interface
i2c_driver_data_t driver_data;
fsm_data_t fsm_data = { 0 };

// Shared memory regions
i2c_queue_handle_t queue_handle;

// This table is responsible for relating the state enum to the state functions.
// I.e. i2c_state_table[0] == i2c_state_table[S_IDLE] == state_idle(*f, *data).
// If you change the state enum and/or add/remove states, make sure you keep this up to date!
i2c_state_func_t *i2c_state_table[NUM_STATES] = { state_idle, state_req,     state_sel_cmd,
                                                  state_cmd,  state_cmd_ret, state_resp };

/**
 * Initialise the i2c master interfaces.
*/
static inline void i2c_setup(void)
{
    LOG_I2C_DRIVER("initialising i2c master interfaces...\n");
    // TODO: check if these bits are correct
    // Initialisation sequence
    regs->ctl |= REG_CTRL_IEN;

    // Set I2C frequency divider for 100 kHz
    // Assuming 24 MHz system clock: 24MHz / 100kHz = 240 divider
    // From IFDR table, IC=0x0F gives divider of 240
    // TODO: check if this is correct
    // NOTE: should be fast-mode (400 MHz)
    // I think this should be 250 actually recheck calculations
    regs->freq = 0x06;

    // Set to master mode
    regs->ctl |= REG_CTRL_MSTA;
}

/**
 * Given a bus interface, retrieve the error code stored in the control register associated.
 * Also gets bytes read and curr token (curr token can be used to find the error location)
 * @return error bit - if the i2c device generates a NACK during writing
 */
static inline bool i2c_get_error(uint8_t *bytes_read, uint8_t *curr_token)
{
    volatile uint32_t ctl = regs->ctl;
    bool err = ctl & (1 << 3);   // bit 3 -> set if error
    *bytes_read = (ctl & 0xF00) >> 8; // bits 8-11 -> number of bytes to read from rdata registers
    *curr_token = (ctl & 0xF0) >> 4; // bits 4-7 -> curr token

    return err;
}

/**
 * Aborts the current operation by generating an I2C STOP command on the I2C bus
 */
int i2c_halt(void)
{
    LOG_I2C_DRIVER("LIST PROCESSOR HALT\n");
    regs->ctl &= ~0x1;
    if ((regs->ctl & 0x1)) {
        LOG_I2C_DRIVER("failed to halt!\n");
        return -1;
    }
    return 0;
}

void init(void)
{
    assert(i2c_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    regs = (volatile struct i2c_regs *)device_resources.regions[0].region.vaddr;
    i2c_setup();

    // Set up driver state and shared regions
    i2c_reset_state(&driver_data);
    queue_handle = i2c_queue_init(config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr);

    microkit_dbg_puts("Driver initialised.\n");
}
 
// 55% duty cycle -> double check fastmode spec
// we always want to target fast mode i2c 
// https://www.nxp.com/docs/en/user-guide/UM10204.pdf

// IMX data sheet
// TS document on i2c
// check linux driver for i2c init
// check this for duty cycle: https://www.nxp.com/docs/en/user-guide/UM10204.pdf
// useful calculator: https://qalculate.github.io/
// functions to change: init, state_cmd, state_cmd_ret -> everything else should be fine


/**
 * S_CMD (command)
 * Initiate work for the current command then go to S_CMD_RET to await device completion.
 * Succeeds: S_SEL_CMD, S_CMD_RET
 * Sucessor(s): S_CMD_RET, S_RESPONSE (error)
 */
void state_cmd(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{

    // TODO: clear all registers first?

    // The following code loops through all available space in the registers their is either:
    // a. no space in a needed register
    // b. the command is over
    // - add meson_token equivalent to token list register
    // - if read or write increment wdata or rdata offset
    // - if write add buffer data into wdata
    // Note: we check <= instead of < for the cmd length because we always need an extra round to
    //       send a STOP token.
    // TODO: check this while condition and match it with meson, check if no space in register
    // TODO: check IBB register before executing anything (poll IBB)
    while (data->rw_idx <= data->active_cmd.data_len) { // Discover next operation
        // Poll IBB register (check if bus is busy)
        // TODO: check that this is correct and that there is no better way to poll
        while (!(regs->status &= (uint16_t) REG_STAT_IBB)) {}

        uint8_t meson_token;
        uint32_t payload_byte;
        // Handle sending start condition
        if (data->await_start) {
            LOG_I2C_DRIVER("Selected START\n");
            // Set to TX (transmit start)
            regs->status |= (uint16_t) REG_STAT_MTX;

            meson_token = MESON_I2C_TOKEN_START;
      
            data->await_start = false;
            // Set bus to busy
            regs->status |= (uint16_t) REG_STAT_IBB;
        }
        // Handle sending address token
        else if (data->await_addr) {
            // TODO: change magic number
            uint32_t transfer_direction = cmd_is_read(cmd) ? 1 : 0;
            meson_token = cmd_is_read(cmd) ? MESON_I2C_TOKEN_ADDR_READ : MESON_I2C_TOKEN_ADDR_WRITE;
            payload_byte = (i2c_curr_addr(data) & 0x7f << 1);
            // Set transfer direction (read is 1 write is 0)
            payload_byte |= transfer_direction;
            data->await_addr = false;
        } 
        // Handle sending stop condition once command has sent all bytes if we need one.
        else if (data->rw_idx >= cmd.data_len) {
            if (data->await_stop) {
                meson_token = MESON_I2C_TOKEN_STOP;
                data->await_stop = false;
            } else {
                // If we don't need a stop condition, skip final iteration.
                break;
            }
            data->rw_idx++;
        } 
        // Handle data transmission
        else {
            // Should be the end of address cycle (TODO: check if this is right)
            // If command is read, switch to RX mode and dummy read from I2C_I2DR
            if (cmd_is_read(cmd) && data->rw_idx == 0) {

            }

            // We are in the middle of a read or write. Pick up where we left off
            if (data->rw_idx == (cmd.data_len - 1) && cmd_is_read(cmd)) {
                meson_token = MESON_I2C_TOKEN_DATA_END;
                // TODO: read
                // meson_token = MESON_I2C_TOKEN_DATA_END;
            } 
            else {
                assert(data->rw_idx < cmd.data_len);
                meson_token = MESON_I2C_TOKEN_DATA;
            }
            // If writing, and this is not the subaddress of a WRRD
            if (!cmd_is_read(cmd)) {
                payload_byte = cmd.payload.data[data->rw_idx]; // Take next byte to write
            }
            data->rw_idx++;
        }
        
        // If data token and we are writing (inc. WRRD) or we are sending an address, load data into data register
        if ((meson_token == MESON_I2C_TOKEN_DATA && !data_direction_rd(data)) || MESON_I2C_TOKEN_ADDR_READ || MESON_I2C_TOKEN_ADDR_WRITE) {
            regs->data = payload_byte;
        }
        
        /* If data token and we are reading (not WRRD write), increment counter of rdata */
        if ((meson_token == MESON_I2C_TOKEN_DATA || meson_token == MESON_I2C_TOKEN_DATA_END) && data_direction_rd(data)) {
            // Note: rdata_offset just makes sure we don't read more than 8 times in
            //       a single transaction as this is the limit of the hardware.
            rdata_offset++;
        }
    }

    // Start list processor
    fsm->next_state = S_CMD_RET;
    fsm->yield = true; // We want to go to sleep awaiting the IRQ coming back to us.
}

/**
 * S_CMD_RET
 * Handle return of data from hardware after S_CMD goes to sleep post-load. Decides whether to
 * continue working on the current command or to return to S_SEL_CMD for a new one.
 *
 * Succeeds: S_CMD
 * Sucessor(s): S_CMD (cmd not finished yet), S_SEL_CMD (cmd finished), S_RESP (error)
 */
void state_cmd_ret(fsm_data_t *f, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{   
    // Note: unlike the meson driver, we can only read one byte at a time since the data register only holds one byte
    // Clear IFF register upon return interrupt
    regs->status &= (uint8_t)(~REG_STAT_IFF);

    // TODO: check that transmission was completed succesfully after interrupt complete
    // Write error detected
    // TODO: doble check this bitmask logic
    // If RXAK = 0, error has occured -> return
    if (!(regs->status & (uint8_t)(REG_STAT_RXAK))) {
        if (curr_token == MESON_I2C_TOKEN_ADDR_READ) {
            data->err = I2C_ERR_NOREAD;
        } else {
            data->err = I2C_ERR_NACK;
        }
        LOG_I2C_DRIVER("token that caused error: %d!\n", curr_token);
        f->next_state = S_RESPONSE;
    } else {
        // Set TXAK to 1 when reading 2nd to last byte
        // TODO: check if index/token write is correct
        if (data->rw_idx == (data->active_cmd.data_len - 1)) {
            regs->ctl |= REG_STAT_TXAK;
        }

        uint8_t value = regs->data;
        data->active_cmd.payload.data[data->bytes_read] = value;
        data->bytes_read++;

        // Decide whether this is the end or to return back to sel_cmd
        // Note: this isn't a signpost error. S_CMD runs for one round extra to send a STOP
        if (data->rw_idx > data->active_cmd.data_len)
            f->next_state = S_SEL_CMD;
        else
            f->next_state = S_CMD;
    }
}

void notified(microkit_channel ch)
{
    // We have only two possible cases for returning to the FSM from this entrypoint:
    // 1. The virt has pinged us. No direct action needed, other than to wake the FSM
    //    if currently idle. If working, will be answered automagically.
    //    (curr state = S_IDLE)
    // 2. IRQ 0 has landed indicating a completed transaction - resume FSM if we expected this.
    //    (curr state = S_CMD_RET)
    // Any other combination requires no direct action as the FSM is still running, or is spurious.
    LOG_I2C_DRIVER("Notified\n");
    if (ch == config.virt.id) {
        LOG_I2C_DRIVER("Notified by virt!\n");
        fsm_virt_notified(&fsm_data);
    } else if (ch == device_resources.irqs[0].id) {
        LOG_I2C_DRIVER("IRQ!\n");
        fsm_cmd_done(&fsm_data);
        microkit_irq_ack(ch);
    } else if (ch == device_resources.irqs[1].id) {
        /* Timeout IRQ */
        LOG_I2C_DRIVER("Timeout!\n");
        // We don't handle this as there is no clear principled way to do so.
        // This IRQ is undocumented and will rapidly be followed by a NACK if
        // a device disappears, so there's no clear reason to do anything here.
        microkit_irq_ack(ch);
    } else {
        LOG_I2C_DRIVER_ERR("unexpected notification on channel %d\n", ch);
    }
}
