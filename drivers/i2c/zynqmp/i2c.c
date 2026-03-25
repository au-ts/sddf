/*
 * Copyright 2026, Skykraft
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/**
 * I2C controller driver for Zynq Ultrascale+ I2C IP block
 * Adapted from OpenTitan implementation for sDDF
 * 
 * A lot of this driver was implemented by matching against
 * the Xilinx driver:
 * https://github.com/Xilinx/embeddedsw/tree/master/XilinxProcessorIPLib/drivers/iicps/src
 */

#include <sddf/i2c/i2c_driver.h>
#include <sddf/i2c/queue.h>
#include <sddf/resources/device.h>
#include "i2c.h"

/* sdfgen */
__attribute__((__section__(".i2c_driver_config"))) i2c_driver_config_t config;
__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

void handle_irq(microkit_channel ch);
void i2c_init(void);
void i2c_reset(void);
int i2c_self_test(void);
int i2c_set_sclk(uint32_t clock_hz);
static inline uint32_t get_tf_fifo_space(void);
void reg_dump(void);

/* Transport */
i2c_queue_handle_t queue_handle;
uintptr_t request_region;
uintptr_t response_region;

/* Internal state */
i2c_driver_data_t driver_data;
fsm_data_t fsm_data = { 0, 0, 0 };

/* State function table */
i2c_state_func_t *i2c_state_table[NUM_STATES] = { state_idle, state_req,     state_sel_cmd,
                                                  state_cmd,  state_cmd_ret, state_resp };

/* Registers */
volatile zynq_i2c_regs_t *regs;

static inline bool bus_is_busy(void)
{
    return ((regs->status & I2C_STAT_BUS_ACTIVE) != 0);
}

static inline bool rx_fifo_not_empty(void)
{
    return ((regs->status & I2C_STAT_RXDV) != 0);
}

static void clear_all_irqs(void)
{
    LOG_I2C_DRIVER("Clearing outstanding IRQs in ISR\n");
    regs->isr = INT_ALL_MASK;
}

/**
 * Enables common interrupts between read/write requests, and also
 * read/write specific interrupts.
 */
static void irqs_enable(bool is_receiver)
{
    /* Enable interrupts we care about */
    if (is_receiver) {
        regs->ier = INT_COMP_MASK | INT_NACK_MASK | INT_TO_MASK | INT_ARB_LOST_MASK | INT_DATA_MASK | INT_RX_OVF_MASK;
    } else {
        regs->ier = INT_COMP_MASK | INT_NACK_MASK | INT_TO_MASK | INT_ARB_LOST_MASK;
    }

    LOG_I2C_DRIVER("Enabled IRQs: imr=0x%x\n", regs->imr);
}

static void irqs_disable(void)
{
    /* Disable interrupts - just mask, don't clear ISR.
     * A new transaction may have been started during fsm() and
     * clearing ISR here would lose that interrupt. */
    regs->idr = INT_ALL_MASK;
}

/**
 * Write a byte to the I2C data register (TX FIFO)
 */
static inline int i2c_write_byte(uint8_t data)
{
    if (get_tf_fifo_space() == 0) {
        LOG_I2C_DRIVER_ERR("TX FIFO full (tf_size=0x%x), cannot write!\n", regs->tf_size);
        return -1;
    }
    regs->i2c_data = data;
    return 0;
}

static inline void i2c_write_addr(i2c_driver_data_t *data)
{
    if (cmd_is_read(data->active_cmd)) {
        LOG_I2C_DRIVER("BEFORE initiating read from slave 0x%02x (ISR=0x%x STATUS=0x%x)\n", i2c_curr_addr(data),
                       regs->isr, regs->status);
    } else {
        LOG_I2C_DRIVER("BEFORE initiating write to slave 0x%02x (ISR=0x%x STATUS=0x%x)\n", i2c_curr_addr(data),
                       regs->isr, regs->status);
    }
    clear_all_irqs();
    irqs_enable(cmd_is_read(data->active_cmd));

    /* Ensure IRQs enable and addr write appear in order */
    THREAD_MEMORY_RELEASE();

    regs->i2c_addr = i2c_curr_addr(data);

    uint32_t isr_immediate = regs->isr;
    uint32_t status_immediate = regs->status;

    if (cmd_is_read(data->active_cmd)) {
        LOG_I2C_DRIVER("Initiated read from slave 0x%02x (ISR=0x%x STATUS=0x%x)\n", i2c_curr_addr(data), isr_immediate,
                       status_immediate);
    } else {
        LOG_I2C_DRIVER("Initiated write to slave 0x%02x (ISR=0x%x STATUS=0x%x)\n", i2c_curr_addr(data), isr_immediate,
                       status_immediate);
    }
}

/**
 * Read a byte from the I2C data register (FIFO)
 */
static inline uint8_t i2c_read_byte(void)
{
    return (uint8_t)(regs->i2c_data & 0xFF);
}

/**
 * Get available space in TX FIFO.
 * In master transmitter mode, tf_size represents bytes in FIFO.
 * In master receiver mode, tf_size represents bytes waiting to be received into FIFO.
 */
static inline uint32_t get_tf_fifo_space(void)
{
    uint32_t tf_size = regs->tf_size & 0xFF;
    uint32_t avail = (tf_size < ZYNQ_FIFO_DEPTH) ? (ZYNQ_FIFO_DEPTH - tf_size) : 0;
    LOG_I2C_DRIVER("TX FIFO: %u bytes used, %u bytes available\n", tf_size, avail);
    return avail;
}

/**
 * Fill the TX FIFO with data bytes.
 * Determine available FIFO space,
 * loads min(available, remaining) bytes, advances rw_idx.
 *
 * @return remaining bytes not yet loaded into FIFO
 */
static uint32_t transmit_fifo_fill(i2c_driver_data_t *data, i2c_cmd_t cmd)
{
    uint32_t tf_size = regs->tf_size & 0xFF;
    uint32_t avail = ZYNQ_FIFO_DEPTH - tf_size;
    uint32_t remaining = cmd.data_len - data->rw_idx;
    uint32_t to_send = (remaining > avail) ? avail : remaining;

    LOG_I2C_DRIVER("transmit_fifo_fill: avail=%u remaining=%u to_send=%u\n", avail, remaining, to_send);

    for (uint32_t i = 0; i < to_send; i++) {
        if (i2c_write_byte(cmd.payload.data[data->rw_idx]) != 0) {
            LOG_I2C_DRIVER_ERR("transmit_fifo_fill: FIFO full at byte %u\n", data->rw_idx);
            break;
        }
        data->rw_idx++;
    }

    return cmd.data_len - data->rw_idx;
}

/**
 * Prepare controller for a new transfer.
 * Follows Xilinx XIicPs_SetupMaster pattern:
 *  - Decides HOLD based on byte count and repeated-start
 *  - Single atomic write to CTRL reg: MS, ACK_EN, NEA, CLR_FIFO, RX/TX_EN, HOLD
 *  - Disables all interrupts (re-enabled later in i2c_write_addr)
 *
 * @param is_receiver    true for master-receive, false for master-transmit
 * @param repeated_start true when bus must be held for a subsequent phase (WRRD, etc.)
 * @return 0 on success, -1 if bus is busy
 */
static int setup_master(bool is_receiver, bool repeated_start)
{
    uint32_t ctrl = regs->ctrl;

    /* Only check bus busy when HOLD is not set */
    if ((ctrl & I2C_CTRL_HOLD) == 0) {
        if (bus_is_busy()) {
            LOG_I2C_DRIVER_ERR("Bus busy in setup_master\n");
            return -1;
        }
    }

    /* Master, ACK_EN, NEA, CLR_FIFO + direction */
    ctrl |= I2C_CTRL_ACK_EN | I2C_CTRL_CLR_FIFO | I2C_CTRL_NA_MODE | I2C_CTRL_MASTER_MODE;

    if (is_receiver) {
        ctrl |= I2C_CTRL_MASTER_RX_EN;
    } else {
        ctrl &= ~I2C_CTRL_MASTER_RX_EN;
    }

    regs->ctrl = ctrl;

    /* Disable all interrupts during setup (re-enabled in i2c_write_addr) */
    irqs_disable();

    LOG_I2C_DRIVER("setup_master(%s, %s): CTRL=0x%08x\n", is_receiver ? "RX" : "TX",
                   repeated_start ? "repeated" : "simple", regs->ctrl);
    return 0;
}

/**
 * Set the transfer size register for a receive operation.
 * Caps at ZYNQ_MAX_TF_SIZE (252) per request, matching Xilinx's
 * XIICPS_MAX_TRANSFER_SIZE = 255 − 3.
 *
 * @param byte_count  total remaining bytes to receive
 * @return number of bytes set for this transfer chunk
 */
static uint32_t setup_tf_reg(uint32_t byte_count)
{
    uint32_t to_read = (byte_count > ZYNQ_MAX_TF_SIZE) ? ZYNQ_MAX_TF_SIZE : byte_count;

    regs->tf_size = to_read;
    LOG_I2C_DRIVER("Set transfer size: %u (remaining: %u)\n", to_read, byte_count);
    return to_read;
}

/**
 * Initiate a master transmit transfer.
 *
 * @return 0 on success, -1 if bus is busy
 */
static int master_send(i2c_driver_data_t *data, i2c_cmd_t cmd)
{
    uint32_t byte_count = cmd.data_len - data->rw_idx;

    /*
     * Set HOLD when transfer spans multiple FIFO loads, or when a
     * repeated START is needed after this phase.
     */
    if (byte_count > ZYNQ_FIFO_DEPTH || cmd_is_wrrd(cmd)) {
        regs->ctrl |= I2C_CTRL_HOLD;
    }

    /* TX setup: CLR_FIFO + direction + disable IRQs */
    if (setup_master(false, cmd_is_wrrd(cmd)) != 0) {
        LOG_I2C_DRIVER_ERR("Bus busy during write setup\n");
        return -1;
    }

    /* Fill FIFO BEFORE initiating transfer */
    transmit_fifo_fill(data, cmd);

    /* Clear ISR, enable TX IRQs, write address to start transfer */
    i2c_write_addr(data);

    data->await_addr = false;
    LOG_I2C_DRIVER("master_send: loaded %u/%u bytes, transfer started\n", data->rw_idx, cmd.data_len);
    return 0;
}

static int master_recv(i2c_driver_data_t *data, i2c_cmd_t cmd)
{
    uint32_t remaining = cmd.data_len - data->rw_idx;

    /*
     * Set HOLD when transfer spans multiple FIFO loads, or when a
     * repeated START is needed after this phase.
     */
    if (remaining > ZYNQ_FIFO_DEPTH || cmd_is_wrrd(cmd)) {
        regs->ctrl |= I2C_CTRL_HOLD;
    } else {
        regs->ctrl &= ~I2C_CTRL_HOLD;
    }

    /* RX setup: CLR_FIFO + direction + HOLD in one write */
    if (setup_master(true, cmd_is_wrrd(cmd)) != 0) {
        LOG_I2C_DRIVER_ERR("Bus busy during read setup\n");
        return -1;
    }

    /* Set transfer size */
    uint32_t to_read = setup_tf_reg(remaining);

    /* Clear ISR, enable IRQs, write address to start transfer */
    i2c_write_addr(data);

    data->rw_idx += to_read;
    data->await_addr = false;
    return 0;
}

/**
 * Set I2C clock frequency (Table 22-27)
 * Reference: Xilinx XIicPs_SetSClk() @ xiicps_options.c:
 * @param clock_hz Desired I2C clock frequency in Hz (e.g. 400000 for 400kHz)
 * @return 0 on success, -1 on failure
 */
int i2c_set_sclk(uint32_t clock_hz)
{
    /* Cannot change clock during transfer */
    if (regs->tf_size != 0) {
        LOG_I2C_DRIVER_ERR("Cannot set clock during active transfer\n");
        return -1;
    }

    uint32_t Div_a;
    uint32_t Div_b;
    uint32_t ActualFscl;
    uint32_t LastError;
    uint32_t BestError;
    uint32_t CurrentError;
    uint32_t CalcDivA;
    uint32_t CalcDivB;
    uint32_t BestDivA;
    uint32_t BestDivB;
    uint32_t FsclHzVar = clock_hz;
    const uint32_t input_clock = ZYNQ_LPD_LSBUS_CLK;

    uint32_t Temp = input_clock / ((uint32_t)22U * FsclHzVar);

    if ((uint32_t)(0U) == Temp) {
        /* Default to 100 KHz if answer is negative or 0*/
        FsclHzVar = 100000;
    }

    /*
	 * If frequency 400KHz is selected, 384.6KHz should be set.
	 * If frequency 100KHz is selected, 90KHz should be set.
	 * This is due to a hardware limitation.
	 */
    if (FsclHzVar > (uint32_t)384600U) {
        FsclHzVar = (uint32_t)384600U;
    }

    if ((FsclHzVar <= (uint32_t)100000U) && (FsclHzVar > (uint32_t)90000U)) {
        FsclHzVar = (uint32_t)90000U;
    }

    /*
	 * TempLimit helps in iterating over the consecutive value of Temp to
	 * find the closest clock rate achievable with divisors.
	 * Iterate over the next value only if fractional part is involved.
	 */
    uint32_t TempLimit = (((input_clock) % ((uint32_t)22 * FsclHzVar)) != (uint32_t)0x0U) ? (Temp + (uint32_t)1U)
                                                                                          : Temp;

    BestError = FsclHzVar;

    BestDivA = 0U;
    BestDivB = 0U;
    for (; Temp <= TempLimit; Temp++) {
        LastError = FsclHzVar;
        CalcDivA = 0U;
        CalcDivB = 0U;

        for (Div_b = 0U; Div_b < 64U; Div_b++) {

            Div_a = Temp / (Div_b + 1U);

            if (Div_a != 0U) {
                Div_a = Div_a - (uint32_t)1U;
            }
            if (Div_a > 3U) {
                continue;
            }
            ActualFscl = (input_clock) / (22U * (Div_a + 1U) * (Div_b + 1U));

            if (ActualFscl > FsclHzVar) {
                CurrentError = (ActualFscl - FsclHzVar);
            } else {
                CurrentError = (FsclHzVar - ActualFscl);
            }

            if (LastError > CurrentError) {
                CalcDivA = Div_a;
                CalcDivB = Div_b;
                LastError = CurrentError;
            }
        }

  /*
		 * Used to capture the best divisors.
		 */
        if (LastError < BestError) {
            BestError = LastError;
            BestDivA = CalcDivA;
            BestDivB = CalcDivB;
        }
    }

    /* Set divisor values */
    uint32_t ctrl = regs->ctrl;
    ctrl &= I2C_CTRL_CLR_DIV_MASK;
    ctrl |= ((BestDivA & I2C_CTRL_DIV_A_MAX) << I2C_CTRL_DIV_A_OFFSET)
          | ((BestDivB & I2C_CTRL_DIV_B_MAX) << I2C_CTRL_DIV_B_OFFSET);
    regs->ctrl = ctrl;

    uint32_t actual_freq = input_clock / (22 * (BestDivA + 1) * (BestDivB + 1));
    LOG_I2C_DRIVER("Clock configured: requested=%u Hz, actual=%u Hz (div_a=%u, div_b=%u)\n", clock_hz, actual_freq,
                   BestDivA, BestDivB);

    /* Digital glitch filter for SCLK/SDA noise */
    regs->gfr = I2C_GFR_RESET_VAL;

    return 0;
}

/**
 * Reset and halt the controller
 * @warning Only call this when transfer is complete or after error!
 * Calling during an active transfer may cause premature termination.
 */
int i2c_halt(void)
{
    LOG_I2C_DRIVER("Halting I2C controller\n");

    /* Clear FIFOs */
    regs->ctrl |= I2C_CTRL_CLR_FIFO;

    /* Clear HOLD bit to release bus */
    // WARNING: This could trigger premature termination if called during transfer!
    regs->ctrl &= ~I2C_CTRL_HOLD;

    /* Spin wait for bus to be free */
    uint32_t timeout = 10000;
    while (bus_is_busy() && timeout > 0) {
        timeout--;
    }

    if (timeout == 0) {
        LOG_I2C_DRIVER_ERR("Fatal! Timeout waiting for bus to be free in halt!\n");
        reg_dump();
        return -1;
    }

    LOG_I2C_DRIVER("I2C controller halted\n");

    return 0;
}

/**
 * Abort transfer and reset the FIFOs
 * 
 * Reference Xilinx XIicPs_Abort() @ xiicps.c
 */
void i2c_abort(void)
{
    uint32_t IntrMaskReg;
    uint32_t IntrStatusReg;
    LOG_I2C_DRIVER("Aborting i2c controller!\n");
 /*
	 * Enter a critical section, so disable the interrupts while we clear
	 * the FIFO and the status register.
	 */
    IntrMaskReg = regs->imr;
    regs->idr = INT_ALL_MASK;

 /*
	 * Reset the settings in config register and clear the FIFOs.
	 */
    regs->ctrl = I2C_CTRL_RESET_MASK | I2C_CTRL_CLR_FIFO;

 /*
	 * Read, then write the interrupt status to make sure there are no
	 * pending interrupts.
	 */
    IntrStatusReg = regs->isr;
    regs->isr = IntrStatusReg;

 /*
	 * Restore the interrupt state.
	 */
    IntrMaskReg = INT_ALL_MASK & (~IntrMaskReg);
    regs->ier = IntrMaskReg;
}

/** 
 * Prepare state for a command. Adapted from opentitan/i2c.c.
*/
void state_cmd(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    LOG_I2C_DRIVER("S_CMD entry\n");

    LOG_I2C_DRIVER("TX FIFO space: %u\n", get_tf_fifo_space());
    LOG_I2C_DRIVER("rw_idx = %u - data_len = %u\n", data->rw_idx, data->active_cmd.data_len);
    i2c_cmd_t cmd = data->active_cmd;
    bool work_done = false;

    /* Check bus readiness - DO NOT clear HOLD or FIFOs here!
     *
     * Error recovery already calls i2c_halt() in handle_irq().
     * Calling it here clears HOLD before read transactions start,
     * which releases the bus prematurely (fatal for WRRD).
     */
    if (data->await_wrrd != WRRD_SUBADDR) {
        /* For new transactions, verify bus is idle */
        if (bus_is_busy()) {
            LOG_I2C_DRIVER_ERR("Bus busy at state_cmd entry, waiting...\n");
            fsm->next_state = S_CMD;
            fsm->yield = true;
            reg_dump();
            return;
        }
    }

    /* Loop while there's work to do:
     * - For writes: TX FIFO space is needed to push data bytes
     * - For reads: TX FIFO space is irrelevant (we set tf_size and write addr)
     */
    while ((cmd_is_read(data->active_cmd) || get_tf_fifo_space() > 0) && data->rw_idx < data->active_cmd.data_len) {
        LOG_I2C_DRIVER("Loop iteration: FIFO space: %u\n", get_tf_fifo_space());

        /* START Condition is implicit with address write, clear the flag */
        if (data->await_start) {
            LOG_I2C_DRIVER("Selected START\n");
            data->await_start = false;
        }

        /* Handle write of sub address for register reads (WRRD flag) */
        if (data->await_wrrd) {
            LOG_I2C_DRIVER("Selecting WRRD\n");

            /* 1. Write address (write of subaddress) */
            if (data->await_wrrd == WRRD_WRADDR) {
                LOG_I2C_DRIVER("WRRD_WRADDR: Writing subaddress byte\n");
                LOG_I2C_DRIVER("WRRD_WRADDR: data[0]=0x%02x, slave_addr=0x%02x\n", cmd.payload.data[0],
                               i2c_curr_addr(data));

                /* Setup master as transmitter, with HOLD set (repeated-start read) */
                setup_master(false, true);

                /* Write subaddress byte to FIFO */
                uint8_t subaddr = cmd.payload.data[0];
                i2c_write_byte(subaddr);
                LOG_I2C_DRIVER("Wrote subaddress: 0x%02x\n", subaddr);

                /* Initiate transfer by writing slave address */
                i2c_write_addr(data);

                data->await_wrrd = WRRD_SUBADDR;
                work_done = true;
                break; /* Wait for write to complete and state_cmd invoked again */
            }
            /* 2. Write subaddress complete, prepare for read phase */
            else if (data->await_wrrd == WRRD_SUBADDR) {
                LOG_I2C_DRIVER("WRRD_SUBADDR: Subaddress write done\n");

                /* Clear any pending interrupts before transitioning to read phase */
                clear_all_irqs();

                data->await_wrrd = 0;
                // Always reset await_start - can't switch back to read otherwise
                data->await_start = true;
                data->await_addr = true;
            }

        } else if (data->await_addr) {
            /* Write address and read bit */
            LOG_I2C_DRIVER("Selected ADDR ... read = %d\n", cmd_is_read(cmd));

            if (cmd_is_read(cmd)) {
                int status = master_recv(data, cmd);

                /* Bus is busy */
                if (status) {
                    fsm->next_state = S_CMD;
                    fsm->yield = true;
                    return;
                }

                work_done = true;
                break;
            } else {
                /* Write: fill FIFO and start transfer */
                int status = master_send(data, cmd);
                if (status) {
                    fsm->next_state = S_CMD;
                    fsm->yield = true;
                    return;
                }
                work_done = true;
                break;
            }
        } else {
            /* We shouldn't be able to reach here */
            LOG_I2C_DRIVER_ERR("S_CMD reached dead else-block. await_wrrd=0, await_addr=false, read=%d\n",
                               cmd_is_read(cmd));
            break;
        }
    }

    // Only await command response if we managed to do something
    if (work_done) {
        fsm->next_state = S_CMD_RET;
    } else {
        LOG_I2C_DRIVER_ERR("Warning: S_CMD exited without progress! Sleeping to retry.\n");
        fsm->next_state = S_CMD;
    }
    fsm->yield = true; // We want to go to sleep awaiting the IRQ coming back to us.
}

void state_cmd_ret(fsm_data_t *f, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    LOG_I2C_DRIVER("S_CMD_RET entry\n");

    i2c_cmd_t cmd = data->active_cmd;

    /* For reads, extract data from RX FIFO */
    if (cmd_is_read(cmd)) {
        while (rx_fifo_not_empty() && data->bytes_read < data->rw_idx) {
            uint8_t value = i2c_read_byte();
            LOG_I2C_DRIVER("Read byte[%u] = 0x%02x\n", data->bytes_read, value);
            data->active_cmd.payload.data[data->bytes_read] = value;
            data->bytes_read++;
        }
    }

    bool transfer_complete = (data->rw_idx >= cmd.data_len);
    bool data_complete = !cmd_is_read(cmd) || (data->bytes_read >= data->rw_idx);

    /* Case 1: Write/Read fully complete */
    if (transfer_complete && data_complete) {
        LOG_I2C_DRIVER("Command complete: %u bytes %s\n", data->rw_idx, cmd_is_read(cmd) ? "read" : "written");

        /* Clear HOLD to STOP */
        if (data->await_stop) {
            LOG_I2C_DRIVER("Clearing HOLD to generate STOP\n");
            regs->ctrl &= ~I2C_CTRL_HOLD;
            data->await_stop = 0;
        }

        f->next_state = S_SEL_CMD;
        f->yield = false;
    /* Case 2: Still waiting on read data */
    } else if (cmd_is_read(cmd) && data->bytes_read < data->rw_idx) {
        f->next_state = S_CMD_RET;
        f->yield = true;
    /* Case 3: Still waiting on writing data */
    } else if (!cmd_is_read(cmd) && data->rw_idx < cmd.data_len) {
        transmit_fifo_fill(data, data->active_cmd);

        /* Clear HOLD when all bytes loaded */
        if (data->rw_idx >= cmd.data_len && data->await_stop) {
            LOG_I2C_DRIVER("All TX data loaded, clearing HOLD for STOP\n");
            regs->ctrl &= ~I2C_CTRL_HOLD;
            data->await_stop = 0;
        }

        LOG_I2C_DRIVER("Write continuation: %u/%u bytes loaded\n", data->rw_idx, cmd.data_len);
        f->next_state = S_CMD_RET;
        f->yield = true;
    /* Case 4: no more work to do here, but command is incomplete */
    } else {
        f->next_state = S_CMD;
        f->yield = false;
    }

    if (cmd_is_read(data->active_cmd)) {
        LOG_I2C_DRIVER("No error. Bytes read = %u / %u (%u) dispatched for command\n", data->bytes_read,
                       data->active_cmd.data_len, data->rw_idx);
    } else {
        LOG_I2C_DRIVER("No error. Bytes written = %u / %u for command\n", data->rw_idx, data->active_cmd.data_len);
    }
}

/* Verify registers are accessible */
int i2c_self_test(void)
{
    uint32_t test_val = 0x5;
    regs->slave_mon = test_val;
    uint32_t read_val = regs->slave_mon & 0xF;

    if (read_val != test_val) {
        LOG_I2C_DRIVER_ERR("Self-test failed: expected 0x%x, got 0x%x\n", test_val, read_val);
        return -1;
    }

    regs->slave_mon = 0x0;
    LOG_I2C_DRIVER("Self-test passed\n");
    return 0;
}

/* Table 22-8: I2C Reset Hardware */
void i2c_reset(void)
{
    LOG_I2C_DRIVER("Resetting I2C controller\n");

    /* Disable interrupts */
    regs->idr = INT_ALL_MASK;

    /* Clear interrupt status */
    uint32_t clear_ints = regs->isr;
    regs->isr = clear_ints;

    /* Clear hold, master enable, acknowledge bits */
    uint32_t ctrl_val = regs->ctrl;
    ctrl_val &= I2C_CTRL_CLEAR_MASK;
    regs->ctrl = ctrl_val;

    /* Reset timeout */
    regs->sclk_to = I2C_TO_RESET_MASK;

    /* Clear transfer size */
    regs->tf_size = I2C_TF_SIZE_RESET_MASK;

    /* Clear status by reading and writing back */
    uint32_t clear_stat = regs->isr;
    regs->isr = clear_stat;

    /* Reset configuration and enable ACK */
    regs->ctrl = I2C_CTRL_RESET_MASK;
    regs->ctrl |= I2C_CTRL_ACK_EN;
}

void reg_dump(void)
{
    LOG_I2C_DRIVER_ERR("=== REGISTER STATE ===\n");
    LOG_I2C_DRIVER_ERR("CTRL      (0x00) = 0x%08x\n", regs->ctrl);
    LOG_I2C_DRIVER_ERR("STATUS    (0x04) = 0x%08x\n", regs->status);
    LOG_I2C_DRIVER_ERR("I2C_ADDR  (0x08) = 0x%08x\n", regs->i2c_addr);
    /* Skip I2C_DATA - reading it pops a byte from the RX FIFO! */
    LOG_I2C_DRIVER_ERR("ISR       (0x10) = 0x%08x\n", regs->isr);
    LOG_I2C_DRIVER_ERR("TF_SIZE   (0x14) = 0x%08x\n", regs->tf_size);
    LOG_I2C_DRIVER_ERR("SLAVE_MON (0x18) = 0x%08x\n", regs->slave_mon);
    LOG_I2C_DRIVER_ERR("SCLK_TO   (0x1C) = 0x%08x\n", regs->sclk_to);
    LOG_I2C_DRIVER_ERR("IMR       (0x20) = 0x%08x\n", regs->imr);
    LOG_I2C_DRIVER_ERR("IER       (0x24) = 0x%08x\n", regs->ier);
    LOG_I2C_DRIVER_ERR("IDR       (0x28) = 0x%08x\n", regs->idr);
    LOG_I2C_DRIVER_ERR("GFR       (0x2C) = 0x%08x\n", regs->gfr);
    LOG_I2C_DRIVER_ERR("--- Decoded Status Bits ---\n");
    LOG_I2C_DRIVER_ERR("  BUS_ACTIVE:  %d\n", !!(regs->status & I2C_STAT_BUS_ACTIVE));
    LOG_I2C_DRIVER_ERR("  RXDV:        %d\n", !!(regs->status & I2C_STAT_RXDV));
    LOG_I2C_DRIVER_ERR("--- Decoded Control Bits ---\n");
    LOG_I2C_DRIVER_ERR("  MASTER_MODE: %d\n", !!(regs->ctrl & I2C_CTRL_MASTER_MODE));
    LOG_I2C_DRIVER_ERR("  RX_ENABLE:   %d\n", !!(regs->ctrl & I2C_CTRL_MASTER_RX_EN));
    LOG_I2C_DRIVER_ERR("  HOLD:        %d\n", !!(regs->ctrl & I2C_CTRL_HOLD));
    LOG_I2C_DRIVER_ERR("  ACK_EN:      %d\n", !!(regs->ctrl & I2C_CTRL_ACK_EN));
    LOG_I2C_DRIVER_ERR("  SLVMON:      %d\n", !!(regs->ctrl & I2C_CTRL_SLVMON));
    LOG_I2C_DRIVER_ERR("  CLR_FIFO:    %d\n", !!(regs->ctrl & I2C_CTRL_CLR_FIFO));
    LOG_I2C_DRIVER_ERR("==========================================\n");
}

/* Table 22-9/Figure 22-3: I2C Setup Master */
void i2c_init(void)
{
    LOG_I2C_DRIVER("Initialising I2C controller\n");
    /* Reset I2C HW */
    i2c_reset();

    /* Wait for bus to be free */
    uint32_t ctrl_val = regs->ctrl;
    if (ctrl_val & I2C_CTRL_HOLD) {
        while (bus_is_busy()) {
            LOG_I2C_DRIVER("Waiting for bus to be free...\n");
        }
    }

    /* Configure master as transmitter */
    regs->ctrl = I2C_CTRL_MASTER_INIT_MASK;

    /* Set I2C clock frequency */
    i2c_set_sclk(ZYNQ_I2C_SCLK_FREQ);

    /* Enable interrupts we care about (assume transmitter by default) */
    bool is_receiver = false;
    irqs_enable(is_receiver);

    LOG_I2C_DRIVER("I2C initialisation complete\n");
}

void init(void)
{
    // Check sdfgen properties
    assert(i2c_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    regs = (volatile zynq_i2c_regs_t *)device_resources.regions[0].region.vaddr;

    LOG_I2C_DRIVER("I2C DRIVER|INFO: Zynq I2C Controller Driver\n");
    LOG_I2C_DRIVER("I2C DRIVER|INFO: Register base: 0x%lx\n", (unsigned long)regs);

    /* Initialise hardware */
    i2c_init();

    /* Run self-test */
    if (i2c_self_test()) {
        LOG_I2C_DRIVER_ERR("Register self-test failed.\n");
        return;
    }

    /* Prepare transport layer */
    queue_handle = i2c_queue_init(config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr);
    i2c_reset_state(&driver_data);

    LOG_I2C_DRIVER("I2C Driver initialised successfully\n");
}

/**
 * Table 22-17: Interrupt Handler
 * Loosely followed as most of the work done in state_cmd_ret() 
 */
void handle_irq(microkit_channel ch)
{
    /* Clear ISR */
    uint32_t isr = regs->isr;
    clear_all_irqs();

    /* Get enabled interrupts (IMR bit=1 means disabled) */
    uint32_t imr = regs->imr;
    uint32_t enabled = isr & ~imr;

    LOG_I2C_DRIVER("IRQ: ISR=0x%x enabled=0x%x\n", isr, enabled);

    /* 	Transfer complete interrupt */
    if (enabled & INT_COMP_MASK) {
        LOG_I2C_DRIVER("Transfer complete interrupt!\n");

        if (fsm_data.curr_state == S_CMD_RET) {
            fsm(&fsm_data);
        }
    }

    /* Data interrupt (for multi-byte read/writes) */
    else if (enabled & INT_DATA_MASK) {
        LOG_I2C_DRIVER("Data available interrupt!\n");

        if (fsm_data.curr_state == S_CMD_RET) {
            fsm(&fsm_data);
        }
    }

    /* Error-case interrupts */

    /* Not acknowledged (NACK) interrupt */
    else if (enabled & INT_NACK_MASK) {
        LOG_I2C_DRIVER("NACK interrupt on %02x! - Status=0x%x\n", regs->i2c_addr, regs->status);
        i2c_halt();

        if (fsm_data.curr_state == S_CMD || fsm_data.curr_state == S_CMD_RET) {
            driver_data.err = I2C_ERR_NACK;
        }
        LOG_I2C_DRIVER("DIAG: CTRL=0x%08x STATUS=0x%08x\n", regs->ctrl, regs->status);
        LOG_I2C_DRIVER("DIAG: TF_SIZE=0x%08x ADDR=0x%02x\n", regs->tf_size, regs->i2c_addr);
        LOG_I2C_DRIVER("DIAG: BUS_ACTIVE=%d RXDV=%d\n", !!(regs->status & I2C_STAT_BUS_ACTIVE),
                       !!(regs->status & I2C_STAT_RXDV));
    }

    /* RX overflow interrupt (received more bytes than space in FIFO)*/
    else if (enabled & INT_RX_OVF_MASK) {
        LOG_I2C_DRIVER("Receive overflow interrupt!");
    }

    /* Timeout interrupt (SCLK low for > timeout time)*/
    else if (enabled & INT_TO_MASK) {
        LOG_I2C_DRIVER("Timeout interrupt!\n");
        i2c_halt();
        driver_data.err = I2C_ERR_TIMEOUT;
    }

    /* Arbitration lost interrupt (master loses bus ownership during transfer )*/
    else if (enabled & INT_ARB_LOST_MASK) {
        /* If this occurs in single-master mode, something is seriously wrong,
         * check hardware configuration: FPGA, pins etc.
         */
        LOG_I2C_DRIVER("Arbitration lost interrupt!\n");

        i2c_abort();
        i2c_init();

        LOG_I2C_DRIVER_ERR("Critical: Controller has lost arbitration!\n");

        driver_data.err = I2C_ERR_OTHER;
    }

    /* Table 22-17: "Clear HOLD if all interrupts attended"
     * (We do this in state_cmd_ret when successful or i2c_halt in errors)
    */

    microkit_irq_ack(ch);
}

void notified(microkit_channel ch)
{
    if (ch == config.virt.id) {
        // Virtual notification from queue
        fsm_virt_notified(&fsm_data);
    } else if (ch == device_resources.irqs[0].id) {
        // Hardware interrupt
        LOG_I2C_DRIVER("Hardware IRQ received\n");
        handle_irq(ch);
    } else {
        microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }

    // Handle errors if in active state
    if (driver_data.err != I2C_ERR_OK && (fsm_data.curr_state == S_CMD || fsm_data.curr_state == S_CMD_RET)) {
        LOG_I2C_DRIVER("Transaction failed! Error code: %u\n", driver_data.err);
        i2c_halt();
        // We are outside the FSM - assign current state not next state.
        fsm_data.curr_state = S_RESPONSE;
        fsm_data.next_state = S_RESPONSE;
        fsm(&fsm_data);
    } else if (driver_data.err != I2C_ERR_OK) {
        LOG_I2C_DRIVER_ERR("Spurious error interrupt! err=%u state=%s\n", driver_data.err,
                           state_to_str(fsm_data.curr_state));
    }
}