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

// Uncomment to enable logging
#define DEBUG_I2C_DRIVER

__attribute__((__section__(".i2c_driver_config"))) i2c_driver_config_t config;
__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

// NOTE: i2c registers on the imx8mq are 16 bit!

// Base addresses: I2C1=0x30A20000, I2C2=0x30A30000, I2C3=0x30A40000, I2C4=0x30A50000
volatile struct imx_i2c_regs *regs;

i2c_driver_data_t driver_data;
fsm_data_t fsm_data = { 0 };
i2c_queue_handle_t queue_handle;

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

    // Set frequency divider for 400 KHz (IC=0x06, divider=60 for 24MHz clock)
    regs->ifdr = 0x06;

    // enable, and turn on interrupts
    regs->i2cr = REG_CR_IEN | REG_CR_IIEN;
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

    microkit_dbg_puts("i.MX8M I2C driver initialised.\n");
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

    // Check if we need to send START condition
    if (data->await_start) {
        // Wait for bus not busy
        while (regs->i2sr & REG_SR_IBB) {}

        // Set master mode and transmit mode (for address phase)
        // MSTA=1 generates START condition
        regs->i2cr |= REG_CR_MSTA | REG_CR_MTX;

        // Calculate address byte with R/W bit
        uint8_t addr_byte = (i2c_curr_addr(data) << 1);
        bool is_read = cmd_is_read(data->active_cmd) && !data->await_wrrd;

        if (is_read) {
            addr_byte |= 0x1;  // Read operation (R/W bit = 1)
        } else {
            addr_byte &= ~0x1; // Write operation (R/W bit = 0)
        }

        LOG_I2C_DRIVER("Sending START + ADDR 0x%02x (read=%u)\n", addr_byte, is_read);

        // Write address to data register - this initiates the transfer
        regs->i2dr = addr_byte;

        data->await_start = false;
        data->await_addr = false;
        fsm->next_state = S_CMD_RET;
        fsm->yield = true;
        return;
    }

    // Handle STOP condition generation
    if (data->rw_idx >= data->active_cmd.data_len) {
        if (data->await_stop) {
            LOG_I2C_DRIVER("Generating STOP\n");
            // Clear MSTA to generate STOP condition
            regs->i2cr &= ~REG_CR_MSTA;
            data->await_stop = false;
            fsm->next_state = S_CMD_RET;
            fsm->yield = true;
            return;
        } else {
            // Command complete without STOP (repeated start follows)
            fsm->next_state = S_SEL_CMD;
            return;
        }
    }

    // Handle data transfer
    if (cmd_is_read(data->active_cmd) && !data->await_wrrd) {
        // --- READ OPERATION ---

        // For the first data byte of a read, we need to switch to receive mode
        // and do a dummy read to initiate the first byte reception
        if (data->rw_idx == 0) {
            // Clear MTX to enter receive mode
            regs->i2cr &= ~REG_CR_MTX;

            // If this is a single byte read, prepare NACK for it
            if (data->active_cmd.data_len == 1) {
                regs->i2cr |= REG_CR_TXAK; // No ACK for single byte
            }

            // Dummy read to initiate first byte reception
            // The byte we read here is garbage/invalid for the first read
            (void)regs->i2dr;

            fsm->next_state = S_CMD_RET;
            fsm->yield = true;
            return;
        }

        // For subsequent bytes, the previous read initiated this byte's reception
        // Set up NACK for last byte when reading second-to-last byte
        if (data->rw_idx == data->active_cmd.data_len - 2) {
            // This is the second-to-last byte, set TXAK for NACK on last byte
            regs->i2cr |= REG_CR_TXAK;
        }

        // Read the data byte (this also initiates next byte reception)
        // Actual reading happens in state_cmd_ret after IIF
        fsm->next_state = S_CMD_RET;
        fsm->yield = true;
        return;

    } else {
        // --- WRITE OPERATION ---

        uint8_t write_byte;

        // Handle write-read subaddress injection
        if (data->await_wrrd) {
            // For WRRD, first byte is the register subaddress
            write_byte = data->active_cmd.payload.data[0];
            data->await_wrrd = false; // WRRD write phase complete

            // After this byte completes, we'll need to do repeated start + read
            // The await_wrrd flag being clear indicates we're in read phase now
            // But first we need to check if there's data after subaddress in the write portion

            // Actually per sDDF protocol: WRRD means write first byte (subaddr), then read
            // So we write one byte, then do repeated start
            LOG_I2C_DRIVER("WRRD: writing subaddress 0x%02x\n", write_byte);
        } else {
            // Normal write or WRRD write portion
            write_byte = data->active_cmd.payload.data[data->rw_idx];
        }

        LOG_I2C_DRIVER("Writing data byte 0x%02x at idx %u\n", write_byte, data->rw_idx);

        regs->i2dr = write_byte;
        data->rw_idx++;

        fsm->next_state = S_CMD_RET;
        fsm->yield = true;
        return;
    }
}

/**
 * S_CMD_RET
 * Handle completion interrupt from hardware. Check status, read data if applicable,
 * and determine next state (continue command, select next command, or error).
 */
void state_cmd_ret(fsm_data_t *f, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    uint16_t status = regs->i2sr;

    LOG_I2C_DRIVER("S_CMD_RET: status=0x%04x\n", status);

    // Check for arbitration lost
    if (status & REG_SR_IAL) {
        LOG_I2C_DRIVER_ERR("Arbitration lost!\n");
        data->err = I2C_ERR_OTHER;
        // Write 1 to clear IAL
        regs->i2sr |= REG_SR_IAL;
        f->next_state = S_RESPONSE;
        return;
    }

    // Check for NACK (RXAK=1 means no ACK received)
    // This applies to address phase and write phases
    if (status & REG_SR_RXAK) {
        LOG_I2C_DRIVER_ERR("NACK received\n");

        // Determine if this was address or data phase
        if (data->rw_idx == 0 && !cmd_is_read(data->active_cmd)) {
            // Address NACK during write
            data->err = I2C_ERR_NACK;
        } else if (data->rw_idx == 0 && cmd_is_read(data->active_cmd)) {
            // Address NACK during read attempt
            data->err = I2C_ERR_NOREAD;
        } else {
            // Data phase NACK
            data->err = I2C_ERR_NACK;
        }

        // Generate STOP and return error
        regs->i2cr &= ~REG_CR_MSTA;
        f->next_state = S_RESPONSE;
        return;
    }

    // Handle read data if applicable
    if (cmd_is_read(data->active_cmd) && data->rw_idx > 0) {
        // Read the received byte
        // Note: for the first byte (rw_idx==0), we did dummy read in state_cmd
        // The byte received is now in the register from the previous transaction
        uint8_t value = regs->i2dr;
        data->active_cmd.payload.data[data->bytes_read] = value;
        LOG_I2C_DRIVER("Read byte 0x%02x at bytes_read=%u\n", value, data->bytes_read);
        data->bytes_read++;
        data->rw_idx++;
    }

    // Check if command is complete
    // For reads: rw_idx tracks progress (0..len)
    // For writes: rw_idx already incremented in state_cmd
    if (data->rw_idx >= data->active_cmd.data_len) {
        if (data->await_stop) {
            // We just sent the STOP condition in state_cmd, wait for completion
            // IIF will be set when STOP completes
            LOG_I2C_DRIVER("STOP complete\n");
        }
        f->next_state = S_SEL_CMD;
    } else {
        // More data to transfer
        f->next_state = S_CMD;
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
        // Clear IIF by writing 0 to it (W1C)
        regs->i2sr &= ~REG_SR_IIF;
        fsm_cmd_done(&fsm_data);
        microkit_irq_ack(ch);
    } else {
        LOG_I2C_DRIVER_ERR("unexpected notification on channel %d\n", ch);
    }
}

