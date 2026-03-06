/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/config.h>
#include <sddf/resources/device.h>
#include <string.h>
#include "driver.h"


__attribute__((__section__(".i2c_driver_config"))) i2c_driver_config_t config;
__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

// NOTE: i2c registers on the imx8mq are 16 bit!

// Base addresses: I2C1=0x30A20000, I2C2=0x30A30000, I2C3=0x30A40000, I2C4=0x30A50000
volatile struct imx_i2c_regs *regs;

i2c_driver_data_t driver_data;
fsm_data_t fsm_data = { 0 };
i2c_queue_handle_t queue_handle;

bool dummy_read = false;

i2c_state_func_t *i2c_state_table[NUM_STATES] = {
    state_idle, state_req, state_sel_cmd, state_cmd, state_cmd_ret, state_resp
};

/**
 * Initialise the i2c master interface for 400KHz fast mode.
 */
static inline void i2c_setup(void)
{
    LOG_I2C_DRIVER("initialising i2c master interface...\n");

    // disable initially
    regs->i2cr = 0;
    LOG_I2C_DRIVER("a\n");

    // clear interrupt flag
    regs->i2sr &= ~REG_SR_IIF;
    LOG_I2C_DRIVER("b\n");

    // Set frequency divider for 400 KHz (IC=0x06, divider=60 for 24MHz clock)
    regs->ifdr = 0x06;
    LOG_I2C_DRIVER("c\n");

    // enable, and turn on interrupts
    regs->i2cr = REG_CR_IEN | REG_CR_IIEN;
    LOG_I2C_DRIVER("done\n");
}

/**
 * Aborts the current operation by generating a STOP condition and disabling master mode.
 */
int i2c_halt(void)
{
    LOG_I2C_DRIVER("I2C HALT\n");

    // Clear MSTA bit to generate STOP
    regs->i2cr &= ~(REG_CR_MSTA | REG_CR_MTX);

    // busy wait for ibb to clear ...
    int timeout = 10000;
    while ((regs->i2sr & REG_SR_IBB) && timeout-- > 0) {}

    if (timeout <= 0) {
        LOG_I2C_DRIVER_ERR("failed to halt - bus busy timeout\n");
        return -1;
    }

    // Reset to idle state (keep IEN and IIEN enabled)
    regs->i2cr = REG_CR_IEN | REG_CR_IIEN;

    return 0;
}

void init(void)
{
    assert(i2c_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1 || device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    regs = (volatile struct imx_i2c_regs *)device_resources.regions[0].region.vaddr;
    i2c_setup();

    i2c_reset_state(&driver_data);
    queue_handle = i2c_queue_init(config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr);

    LOG_I2C_DRIVER("i.MX8M I2C driver initialised.\n");
}

/**
 * Send a start condition. This method should short circuit other writes to the CR register.
 */
static inline void imx_i2c_start(bool repeat) {
    // Update dummy read flag upon switch to MTX
    dummy_read = false;
    if (!repeat) {
        regs->i2cr |= REG_CR_MSTA;
        // wait until bus is clear
        while (regs->i2sr & REG_SR_IBB) {
            LOG_I2C_DRIVER("AHHHHH AHHH OHH MY GOD AHHHH\n");
        }

        // write other start flags
        regs->i2cr |= REG_CR_MTX | REG_CR_IIEN;
    } else {
        regs->i2cr |= REG_CR_RSTA;
    }

    // Always enable TXAK at start of a transaction.
    regs->i2cr &= ~REG_CR_TXAK;
}

/**
 * After sending an address+start OR a data byte, call this function
 * to check if an acknowledgement is received.
 *
 * This is required as the hardware will only generate an interrupt on
 * the successful completion of a transfer.
 */
static inline bool imx_i2c_ackd(void) {
    // TODO: figure out if a busy wait is required
    return ((regs->i2sr & REG_SR_RXAK) == 0);
}

/**
 * S_CMD (command)
 * Initiate a single bus operation (START, data byte, or STOP) then yield to await IRQ completion.
 * The imx8mq I2C controller operates byte-by-byte, not as a list processor.
 */
void state_cmd(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    LOG_I2C_DRIVER("S_CMD: rw_idx=%u, len=%u, await_start=%u, await_stop=%u\n",
                   data->rw_idx, data->active_cmd.data_len, data->await_start, data->await_stop);

    // Sanity: if IAL (arbitration lost) is ever asserted, die. This should never happen for now,
    // as our protocol currently doesn't support arbitration.
    if (regs->i2sr & REG_SR_IAL) {
        LOG_I2C_DRIVER_ERR("Arbitration lost! This should never happen as we do not support multi master!\n");
        LOG_I2C_DRIVER_ERR("Dying now.\n");
        // clear IAL
        regs->i2sr &= ~REG_SR_IAL;
        data->err = I2C_ERR_OTHER;
        fsm->next_state = S_RESPONSE;
        return;
    }

    // invariant: these tmp registers are unused if we imx_i2c_start() as the start
    //            op needs to directly touch the registers.
    uint32_t i2cr_tmp = regs->i2cr;
    uint32_t i2dr_tmp = regs->i2dr;
    bool do_i2dr_write = false;
    bool do_i2cr_write = false;
    if (data->await_start) {
        LOG_I2C_DRIVER("Sending start condition...\n");
        // This is a repeated start if await_addr is not set.
        bool is_repeat = (data->await_addr == 0);

        // Sanity: if a write-read is pending, this repeated start is invalid.
        // The virt should handle this, but on the imx this condition is completely
        // unhandleable so we check again.
        assert(!(is_repeat && data->await_wrrd));

        imx_i2c_start(is_repeat);
        data->await_start = false;
        fsm->yield = false;
        // If we're here, i2c_start has already waited until ibb=0.
        // Return to re-enter this state and check if arbitration loss occured.
        return;
    }

    // Addressing stage
    if (data->await_wrrd) {
        // first: handle sending initial address.
        // invariant: start condition already set
        LOG_I2C_DRIVER("Selected WRRD\n");

        if (data->await_wrrd == WRRD_WRADDR) {
            // Write address to data register. read bit = 0
            i2dr_tmp = i2c_curr_addr(data) << 1;
            do_i2dr_write = true;
            // invariant: mtx already set from await_start
        } else if (data->await_wrrd == WRRD_SUBADDR) {
            // Write sub address byte
            uint8_t payload_byte = data->active_cmd.payload.data[0];
            i2dr_tmp = payload_byte;
            do_i2dr_write = true;
            LOG_I2C_DRIVER("WRRD: sending address byte %u\n", payload_byte);
        } else {
            LOG_I2C_DRIVER("WRRD: sending repeat start and looping\n");
            // Send a new start condition and leave await_addr to set up the read
            // for us.
            imx_i2c_start(true);
            LOG_I2C_DRIVER("WRRD: ... done!\n");
            fsm->yield = false;
            data->await_wrrd = 0;
            // Re-enter state to check for arb. loss and continue.
            return;
        }
        data->await_wrrd--;

    } else if (data->await_addr) {
        LOG_I2C_DRIVER("Primary addressing stage...\n");
        // Calculate address byte with R/W bit
        uint8_t addr_byte = (i2c_curr_addr(data) << 1);
        bool is_read = cmd_is_read(data->active_cmd);

        if (is_read) {
            addr_byte |= 0x1;  // Read operation (R/W bit = 1)
        } else {
            addr_byte &= ~0x1; // Write operation (R/W bit = 0)
        }

        LOG_I2C_DRIVER("Sending ADDR 0x%02x (read=%u)\n", i2c_curr_addr(data), is_read);

        // Write address to data register - this initiates the transfer
        i2dr_tmp = addr_byte;
        do_i2dr_write = true;
        data->await_addr = false;

    // Data transmission and end
    } else {
        // read case
        if (cmd_is_read(data->active_cmd)) {
            // For the first data byte of a read, we need to switch to receive mode
            // and do a dummy read to initiate the first byte reception
            if (dummy_read == false) {
                // Clear MTX to enter receive mode
                i2cr_tmp &= ~REG_CR_MTX;
                do_i2cr_write = true;

                // If this is a single byte read, prepare NACK for it
                if (data->active_cmd.data_len == 1) {
                    i2cr_tmp |= REG_CR_TXAK; // No ACK for single byte
                }

                // Dummy read to initiate first byte reception
                // The byte we read here is garbage/invalid for the first read.
                // Store dummy byte in this buffer to avoid optimising out...
                // TODO: check for fencepost error here.
                data->active_cmd.payload.data[0] = (uint8_t) regs->i2dr;
                LOG_I2C_DRIVER("MTX->RX dummy read completed...\n");
                dummy_read = true;
            }

            // We must send a stop just before reading the very last byte
            if (data->rw_idx >= data->active_cmd.data_len - 1) {
                if (data->await_stop) {
                    LOG_I2C_DRIVER("Generating STOP (read)\n");
                    // Clear MSTA and MTX to generate STOP condition
                    // Use real register here as this must happen strictly
                    // BEFORE doing the read.
                    do_i2cr_write = true;
                    i2cr_tmp &= ~REG_CR_MSTA;
                    i2cr_tmp &= ~REG_CR_MTX;
                    data->await_stop = false;
                } else {
                    LOG_I2C_DRIVER("Command complete, skipping back to S_SEL_CMD\n");
                    // Command complete without STOP (repeated start follows)
                    fsm->next_state = S_SEL_CMD;
                    return;
                }
            }

            // Set up NACK for last byte when reading second-to-last byte
            if (data->rw_idx == data->active_cmd.data_len - 2) {
                // This is the second-to-last byte, set TXAK for NACK on last byte
                i2cr_tmp |= REG_CR_TXAK;
                do_i2cr_write = true;
            }

            // Real read: simply store result directly. We are effectively saving
            // the result of the previous read data kick.
            data->active_cmd.payload.data[data->bytes_read] = (uint8_t) regs->i2dr;
            LOG_I2C_DRIVER("Reading byte 0x%02x at idx %u\n",
                           data->active_cmd.payload.data[data->bytes_read], data->rw_idx);
            data->bytes_read++;
            data->rw_idx++;

        } else {
            // --- WRITE OPERATION ---
            uint8_t write_byte;
            write_byte = data->active_cmd.payload.data[data->rw_idx];

            // Generate stop just after sending last byte.
            if (data->rw_idx >= data->active_cmd.data_len-1) {
                if (data->await_stop) {
                    LOG_I2C_DRIVER("Generating STOP (read)\n");
                    // Clear MSTA and MTX to generate STOP condition
                    i2cr_tmp &= ~REG_CR_MSTA;
                    i2cr_tmp &= ~REG_CR_MTX;
                    do_i2cr_write = true;
                    data->await_stop = false;
                } else {
                    // TODO: check if this is needed, we probably can't get here.
                    LOG_I2C_DRIVER("Command complete, skipping back to S_SEL_CMD\n");
                    // Command complete without STOP (repeated start follows)
                    fsm->next_state = S_SEL_CMD;
                    return;
                }
            }

            LOG_I2C_DRIVER("Writing data byte 0x%02x at idx %u\n", write_byte, data->rw_idx);
            regs->i2dr = write_byte;
            do_i2dr_write = true;
            data->rw_idx++;
        }
    }

    // Only write if required. Writing to the DR in read mode is UB, and unneeded writes to CR
    // may have side effects.
    // Important: write DR FIRST.
    if (do_i2dr_write) {
        regs->i2dr = i2dr_tmp;
    }
    if (do_i2cr_write) {
        regs->i2cr = i2cr_tmp;
    }
    // We should always sleep and go to CMD_RET unless we decided to return earlier to a
    // different state.
    fsm->next_state = S_CMD_RET;
    fsm->yield = true;
    return;
}

/**
 * S_CMD_RET
 * Handle completion interrupt from hardware. Check status, read data if applicable,
 * and determine next state (continue command, select next command, or error).
 */
void state_cmd_ret(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    // Clear interrupt
    regs->i2sr &= ~REG_SR_IIF;
    uint16_t status = regs->i2sr;

    LOG_I2C_DRIVER("S_CMD_RET: status=0x%04x\n", status);

    // check arbitration, just in case.
    if (status & REG_SR_IAL) {
        LOG_I2C_DRIVER_ERR("Arbitration lost!\n");
        data->err = I2C_ERR_OTHER;
        // clear IAL
        regs->i2sr &= ~REG_SR_IAL;
        fsm->next_state = S_RESPONSE;
        return;
    }

    // Check for NACK (RXAK=1 means no ACK received)
    // This applies to address phase and write phases
    if (status & REG_SR_RXAK) {
        // Don't print this as an error, not useful usually.
        LOG_I2C_DRIVER("NACK!\n");
        data->err = I2C_ERR_NACK;

        // Generate STOP and return error
        regs->i2cr &= ~(REG_CR_MSTA | REG_CR_MTX);
        fsm->next_state = S_RESPONSE;
        return;
    }

    // Check if command is complete
    if (data->rw_idx >= data->active_cmd.data_len - 1) {
        // We just sent the STOP condition in state_cmd, wait for completion
        // IIF will be set when STOP completes
        LOG_I2C_DRIVER("STOP complete\n");
        fsm->next_state = S_SEL_CMD;

        // Clean up
        i2c_setup();
    } else {
        // More data to transfer
        fsm->next_state = S_CMD;
    }
}

void notified(microkit_channel ch)
{
    LOG_I2C_DRIVER("Notified on channel %d\n", ch);

    if (ch == config.virt.id) {
        LOG_I2C_DRIVER("Notified by virt\n");
        fsm_virt_notified(&fsm_data);
    } else if (ch == device_resources.irqs[0].id) {
        LOG_I2C_DRIVER("I2C IRQ\n");
        fsm_cmd_done(&fsm_data);
        microkit_irq_ack(ch);
    } else {
        LOG_I2C_DRIVER_ERR("unexpected notification on channel %d\n", ch);
    }
}

