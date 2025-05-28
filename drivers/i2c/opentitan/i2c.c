/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// I2C controller (master) driver for the OpenTitan I2C IP block
// (https://opentitan.org/book/hw/ip/i2c/). Currently uses the memory map
// for the Cheshire SoC targeting the Digilent Genesys2, but this should
// be trivial to adapt for other boards/SoCs.
// https://github.com/lowRISC/opentitan/blob/9f497f6339b4484fc5b7e5dc5d4bc63f55ec3c35/hw/ip/i2c/doc/_index.md
// WARNING: This driver is for the OpenTitan commit above with Cheshire patches applied!
//          Cheshire applies several patches to adapt peripherals.


#include <sddf/i2c/i2c_driver.h>
#include <sddf/i2c/queue.h>
#include <sddf/resources/device.h>
#include "cheshire-i2c.h"   // Alternate devices should replace this include and substitute
#include "i2c.h"

/* sdfgen */
__attribute__((__section__(".i2c_driver_config"))) i2c_driver_config_t config;
__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

/* IRQs */
// NAK *must* be lowest ID for correctness!
#define IRQ_NAK_CH              (device_resources.irqs[0].id)
#define IRQ_RXTHRESH_CH         (device_resources.irqs[1].id)
#define IRQ_FMTTHRESH_CH        (device_resources.irqs[2].id)
#define IRQ_CMD_COMPLETE_CH     (device_resources.irqs[3].id)
#define IRQ_BAD_STOP_CH         (device_resources.irqs[4].id)
#define IRQ_TIMEOUT_CH          (device_resources.irqs[5].id)

/* Transport */
i2c_queue_handle_t queue_handle;
uintptr_t request_region;
uintptr_t response_region;

/* Internal state */
i2c_driver_data_t driver_data;
fsm_data_t fsm_data = { 0, 0, 0 };

// This table is responsible for relating the state enum to the state functions.
// I.e. i2c_state_table[0] == i2c_state_table[S_IDLE] == state_idle(*f, *data).
// If you change the state enum and/or add/remove states, make sure you keep this up to date!
i2c_state_func_t *i2c_state_table[NUM_STATES] = { state_idle, state_req,     state_sel_cmd,
                                                  state_cmd,  state_cmd_ret, state_resp };

/* Registers */
volatile opentitan_i2c_regs_t *regs;

/* Clock value calculations and timing*/
i2c_timing_params_t timing_params = { .t_high_min = (MAX(((T_HIGH_MIN) / (T_CLK)), 4)),
                                      .t_low_min = (MAX(((T_LOW_MIN) / (T_CLK)), 4)),
                                      .t_hd_dat_min = (MAX(((T_HD_DAT_MIN) / (T_CLK)), 1)),
                                      .t_hd_sta_min = (((0 + T_HD_STA_MIN) / (T_CLK))),
                                      .t_su_sta_min = ((0 + T_SU_STA_MIN) / (T_CLK)),
                                      .t_buf_min = ((0 + T_BUF_MIN) / (T_CLK)),
                                      .t_sto_min = ((0 + T_SU_STO_MIN) / (T_CLK)),
                                      .t_r = ((0 + T_RISE) / (T_CLK)),
                                      .t_f = ((0 + T_FALL) / (T_CLK)),
                                      .t_h = 0,
                                      .t_l = 0 };

static inline bool fmt_fifo_empty(void)
{
    return ((regs->status & I2C_STATUS_FMTEMPTY_BIT) != 0);
}

static inline bool rx_fifo_not_empty()
{
    return ((regs->status & I2C_STATUS_RXEMPTY_BIT) == 0);
}

/**
 * Start the host running.
 */
static inline void i2c_start_host(void) {
    regs->ctrl |= (I2C_CTRL_ENHOST_BIT);
}

/**
 * Stop the host while preserving FMT FIFO status.
 */
static inline void i2c_stop_host(void) {
    regs->ctrl &= ~(I2C_CTRL_ENHOST_BIT);
}
/**
 * Reset the FIFOs and control register. Shouldn't overwrite anything from `init`
 */
int i2c_halt(void)
{
    i2c_stop_host();

    // Reset all fifos
    regs->fifo_ctrl |= (I2C_FIFO_CTRL_FMTRST_BIT);
    regs->fifo_ctrl |= (I2C_FIFO_CTRL_RXRST_BIT);
    regs->fifo_ctrl |= (I2C_FIFO_CTRL_ACQRST_BIT);
    regs->fifo_ctrl |= (I2C_FIFO_CTRL_TXRST_BIT);

    while (regs->ctrl & I2C_CTRL_ENHOST_BIT) {}
    return 0;
}

static inline void clear_irq(uint32_t irq_mask) {
    regs->intr_state = irq_mask;
}

static inline void load_timing_params(i2c_timing_params_t *p)
{
    uint32_t timing0 = ((timing_params.t_h << I2C_TIMING0_THIGH_OFFSET) & I2C_TIMING0_THIGH_MASK)
                     | ((timing_params.t_l << I2C_TIMING0_TLOW_OFFSET) & I2C_TIMING0_TLOW_MASK);
    regs->timing0 = timing0;

    uint32_t timing1 = ((timing_params.t_r << I2C_TIMING1_T_R_OFFSET) & I2C_TIMING1_T_R_MASK)
                     | ((timing_params.t_f << I2C_TIMING1_T_F_OFFSET) & I2C_TIMING1_T_F_MASK);
    regs->timing1 = timing1;

    int32_t timing2 = ((timing_params.t_su_sta_min << I2C_TIMING2_TSU_STA_OFFSET) & I2C_TIMING2_TSU_STA_MASK)
                    | ((timing_params.t_hd_sta_min << I2C_TIMING2_THD_STA_OFFSET) & I2C_TIMING2_THD_STA_MASK);
    regs->timing2 = timing2;

    uint32_t timing3 = ((timing_params.t_su_dat_min << I2C_TIMING3_TSU_DAT_OFFSET) & I2C_TIMING3_TSU_DAT_MASK)
                     | ((timing_params.t_hd_dat_min << I2C_TIMING3_THD_DAT_OFFSET) & I2C_TIMING3_THD_DAT_MASK);
    regs->timing3 = timing3;

    uint32_t timing4 = ((timing_params.t_sto_min << I2C_TIMING4_TSU_STO_OFFSET) & I2C_TIMING4_TSU_STO_MASK)
                     | ((timing_params.t_buf_min << I2C_TIMING4_T_BUF_OFFSET) & I2C_TIMING4_T_BUF_MASK);
    regs->timing4 = timing4;
}

/**
 * Write a byte to the FMT FIFO.
 * @arg data: byte to write to FIFO
 * @arg flags: fmt_flags struct
*/
int i2c_fmt_write(uint8_t data, fdata_fmt_flags_t *flags)
{
    // Parse flags
    // Validate using minterm function - if readb=X, rcont=Y, stop=W, nakok=Z, then
    // F = !X!Y + !W!Z + W!ZX!Y
    bool flags_valid = ((!flags->readb && !flags->rcont) || (!flags->stop && flags->nakok)
                        || (flags->stop && !flags->nakok && flags->readb && !flags->rcont));
    if (!flags_valid) {
        LOG_I2C_DRIVER_ERR("Invalid fmt flags supplied to sddf_i2c_write! Combination cannot be represented "
                       "by hardware!");
        return -1;
    }
    uint32_t addr_fdata = (data)&I2C_FDATA_FBYTE_MASK;

    // Apply flags.
    // NOTE: these 1 bit masks can also be used as offsets with a boolean to set the bit
    //       appropriately.
    addr_fdata |= (flags->stop << I2C_FDATA_STOP_OFFSET) | (flags->rcont << I2C_FDATA_RCONT_OFFSET)
                | (flags->start << I2C_FDATA_START_OFFSET) | (flags->readb << I2C_FDATA_READB_OFFSET)
                | (flags->nakok << I2C_FDATA_NAKOK_OFFSET);

    regs->fdata = addr_fdata;
    return 0;
}

static inline uint32_t get_fmt_fifo_lvl(void)
{
    return (regs->host_fifo_status & I2C_FIFO_STATUS_FMTLVL_MASK) >> I2C_FIFO_STATUS_FMTLVL_OFFSET;
}

static inline uint32_t get_rx_fifo_lvl(void)
{
    return (regs->host_fifo_status & I2C_FIFO_STATUS_RXLVL_MASK) >> I2C_FIFO_STATUS_RXLVL_OFFSET;
}

void state_cmd(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    LOG_I2C_DRIVER("S_CMD entry\n");

    LOG_I2C_DRIVER("fmt fifo level: %u\n", get_fmt_fifo_lvl());
    LOG_I2C_DRIVER("rw_idx = %u - data_len = %u\n", data->rw_idx, data->active_cmd.data_len);
    i2c_cmd_t cmd = data->active_cmd;
    bool work_done = false;

    // Wait until FIFOs are empty
    i2c_halt();
    while(!fmt_fifo_empty()) {}

    // Only load data while the host isn't running.
    i2c_stop_host();

    // The following code loops through all available space in the registers there is either:
    // a. no space in a needed register (just FMT fifo in this case)
    // b. the command is over
    while (get_fmt_fifo_lvl() < OPENTITAN_I2C_FIFO_DEPTH && data->rw_idx < data->active_cmd.data_len) {
        LOG_I2C_DRIVER("fmt fifo level: %u\n", get_fmt_fifo_lvl());
        fdata_fmt_flags_t flags = { 0, 0, 0, 0, 0 };
        uint8_t fmt_byte = 0;

        // Handle sending start condition
        if (data->await_start) {
            LOG_I2C_DRIVER("Selected START\n");
            flags.start = 1;
            data->await_start = false;
        }

        // Handle sending write of sub address for register reads (WRRD flag)
        if (data->await_wrrd) {
            // Write-read/addr works differently on this platform than token-based ones.
            // There's no explicit addressing operation, we instead need to just write
            // the address and read bit
            LOG_I2C_DRIVER("Selecting WRRD\n");

            // Steps completed sequentially
            // 1. Write address
            if (data->await_wrrd == WRRD_WRADDR) {
                // Make fmt op: write address byte, leaving read bit as zero
                fmt_byte = (i2c_curr_addr(data) & 0x7) << 1;
                data->await_wrrd--;
            // 2. Write subaddress
            } else if (data->await_wrrd == WRRD_SUBADDR) {
                // Make fmt op: write sub-address byte
                fmt_byte = cmd.payload.data[0];
                LOG_I2C_DRIVER("WRRD Register subaddress: %X\n", cmd.payload.data[0]);
                flags.readb = 0;
                data->await_wrrd = 0;   // We don't need to resend the start condition on this platform
                // Always reset await_start - can't switch back to read otherwise
                data->await_start = true;
            }

        } else if (data->await_addr) {
            // Write address and read bit
            LOG_I2C_DRIVER("Selected ADDR ... read = %d\n", cmd_is_read(cmd));
            fmt_byte = ((i2c_curr_addr(data) << 1) & 0xFE) | ((cmd_is_read(cmd) != 0) << 7);
            data->await_addr = false;

        // Handle writing data
        } else {
            LOG_I2C_DRIVER("Resuming in-progress read/write. rd=%d remaining=%d\n", cmd_is_read(cmd),
                       cmd.data_len - data->rw_idx);
            // Send stop if needed (this is last op of command)
            if (data->await_stop && data->rw_idx == cmd.data_len - 1) {
                flags.stop = 1;
                data->await_stop = 0;
            }

            if (cmd_is_read(cmd)) {
                // Reads replace data byte with an integer of bytes to read
                flags.readb = 1;
                fmt_byte = MIN(cmd.data_len - data->rw_idx, OPENTITAN_I2C_READ_MAX);
                LOG_I2C_DRIVER("\t reading %u bytes\n", fmt_byte);
                data->rw_idx += fmt_byte;
                assert(data->rw_idx <= cmd.data_len);
                // Always set continuing read unless this is the final read of this command
                flags.rcont = !((data->rw_idx < cmd.data_len));
            } else {
                // Writes insert a single byte to write
                fmt_byte = cmd.payload.data[data->rw_idx];
                LOG_I2C_DRIVER("\t writing %u\n", fmt_byte);
                data->rw_idx++;
            }
        }
        assert(!i2c_fmt_write(fmt_byte, &flags));
        work_done = true;
    }
    i2c_start_host();
    // Only await command response if we managed to do something. In the event that the FMT
    // fifo had no room, we need to go to sleep until there is room and try again.
    if (work_done) {
        fsm->next_state = S_CMD_RET;
    } else {
        LOG_I2C_DRIVER_ERR("Warning: S_CMD exited without progress! Sleeping to retry.");
        fsm->next_state = S_CMD;
    }
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
    LOG_I2C_DRIVER("S_CMD_RET: rx fifo lvl = %u\n", get_rx_fifo_lvl());
    // Extract read data as long as we should have something here
    while (cmd_is_read(data->active_cmd) && rx_fifo_not_empty()) {
        // Get bytes_read amount of read data,copy data into return buffer
        uint8_t value = regs->rdata & 0xFF; // Bytes in low 8 of rdata register.
        LOG_I2C_DRIVER("loading into buffer %p value[%u] 0x%x\n", data->active_cmd.payload.data,
                       data->bytes_read, value);
        data->active_cmd.payload.data[data->bytes_read] = value;
        data->bytes_read++;
    }
    // Case 1: write fully complete or read complete and all bytes returned
    if (data->rw_idx >= data->active_cmd.data_len
        && (!cmd_is_read(data->active_cmd) || (data->bytes_read == data->rw_idx))) {
        f->next_state = S_SEL_CMD;
        f->yield = false;
    // Case 2: awaiting read return
    } else if (cmd_is_read(data->active_cmd) && data->bytes_read < data->rw_idx) {
        // Go to sleep until next IRQ (more rx data)
        f->next_state = S_CMD_RET;
        microkit_irq_ack(IRQ_RXTHRESH_CH);
        f->yield = true; //
    // Case 3: no more work to do here, but command is incomplete
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

void init(void)
{
    // Check sdfgen properties
    assert(i2c_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 6);
    assert(device_resources.num_regions == 1);

    regs = (volatile opentitan_i2c_regs_t *)device_resources.regions[0].region.vaddr;

    LOG_I2C_DRIVER("I2C DRIVER|INFO: Timing parameters configuration:\n");
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_high_min = %u\n", timing_params.t_high_min);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_low_min = %u\n", timing_params.t_low_min);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_hd_dat_min = %u\n", timing_params.t_hd_dat_min);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_hd_sta_min = %u\n", timing_params.t_hd_sta_min);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_su_sta_min = %u\n", timing_params.t_su_sta_min);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_buf_min = %u\n", timing_params.t_buf_min);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_sto_min = %u\n", timing_params.t_sto_min);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_r = %u\n", timing_params.t_r);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_f = %u\n", timing_params.t_f);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_h = %u\n", timing_params.t_h);
    LOG_I2C_DRIVER("I2C DRIVER|INFO: \t t_l = %u\n", timing_params.t_l);

    // Perform initial set up - calculate and validate timing parameters.
    // If any of the below conditions are not true, the device cannot initialise!
    assert(timing_params.t_hd_dat_min >= 1);
    assert(timing_params.t_hd_sta_min > timing_params.t_hd_dat_min);
    assert(timing_params.t_buf_min > timing_params.t_hd_dat_min);

    // Calculate periods - use device-supplied if faster than minimum.
    uint32_t period = MAX(((I2C_SCL_MIN_T) / (T_CLK)), ((SCL_PERIOD) / (T_CLK)));

    // T_H + T_L >= PERIOD - T_F - T_R
    // -> find T_H and T_L such that they fit and achieve duty cycle defined by board.
    // t_h = ( 100 * (T-T_F-T_R) ) / (duty_cycle*100)
    timing_params.t_h = ((100 * (period - T_FALL - T_RISE)) / (DUTY_100X));

    // t_l = ( 100 * (T-T_F-T_R) ) / ((1 - duty_cycle)*100)
    timing_params.t_l = ((100 * (period - T_FALL - T_RISE)) / (100 - DUTY_100X));

    // Check values are valid
    assert(timing_params.t_h >= timing_params.t_high_min);
    assert(timing_params.t_l >= timing_params.t_low_min);

    // Load timing parameters into registers
    load_timing_params(&timing_params);

    // Set up control register -> disable everything and reset all FIFOs.
    i2c_halt();

    // Set up interrupts
    regs->intr_enable |= I2C_INTR_ENABLE_FMT_THRESHOLD_BIT;
    regs->intr_enable |= I2C_INTR_ENABLE_RX_THRESHOLD_BIT;
    regs->intr_enable |= I2C_INTR_ENABLE_NAK_BIT;
    regs->intr_enable |= I2C_INTR_ENABLE_CMD_COMPLETE_BIT;
    regs->intr_enable |= I2C_INTR_ENABLE_UNEXP_STOP_BIT;
    regs->intr_enable |= I2C_INTR_ENABLE_HOST_TIMEOUT_BIT;

    // Configure FIFO interrupt thresholds.
    // FMT: interrupt once emptied.
    // RX: interrupt if 1 or more entries present
    // Both values require 0 in their respective fields, and this is unfortunately not documented
    // anywhere human readable. See `i2c.hjson` from opentitan.
    regs->fifo_ctrl &= (~I2C_FIFO_CTRL_RXILVL_MASK);
    regs->fifo_ctrl &= (~I2C_FIFO_CTRL_FMTILVL_MASK);

    // Prepare transport layer
    queue_handle = i2c_queue_init(config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr);
    i2c_reset_state(&driver_data);
    LOG_I2C_DRIVER("Driver initialised.\n");
}

void notified(microkit_channel ch)
{
    assert(driver_data.err == I2C_ERR_OK);
    if (ch == config.virt.id) {
        fsm_virt_notified(&fsm_data);
    } else if (ch == IRQ_FMTTHRESH_CH) {
        // Asserted when FMT FIFO has < 1 entry.
        LOG_I2C_DRIVER("IRQ_FMTTHRESH\n");
        clear_irq(I2C_INTR_STATE_FMT_THRESHOLD_BIT);
        microkit_irq_ack(ch);

        // We can ignore this IRQ unless we are in S_CMD and awaiting commands to process
        // (i.e. the FMT FIFO was full last time we tried to push commands)
        if (fsm_data.curr_state == S_CMD) {
            fsm(&fsm_data);
        }
    } else if (ch == IRQ_CMD_COMPLETE_CH) {
        // Asserted when the hardware is finished processing a command sequence.
        // We must wake up and run the state machine if we were awaiting this.
        LOG_I2C_DRIVER("IRQ_CMD_COMPLETE\n");
        LOG_I2C_DRIVER("fmt fifo level: %u\n", get_fmt_fifo_lvl());
        clear_irq(I2C_INTR_STATE_CMD_COMPLETE_BIT);
        if (fsm_data.curr_state == S_CMD_RET) {
            fsm(&fsm_data);
        } else {
            LOG_I2C_DRIVER("Warning: received spurious CMD_COMPLETE irq!\n");
        }
        microkit_irq_ack(ch);
    } else if (ch == IRQ_RXTHRESH_CH) {
        // Asserted when RX FIFO has > 0 entries OR command is done. We only need to
        // use this IRQ if we went back to sleep in S_CMD_RET awaiting commands.
        // It is an invariant that this IRQ should only ever arrive while we're in S_CMD_RET
        // if the above case occurs, as if the command completes without needing this it will
        // move back to S_CMD before the next IRQ arrives.
        LOG_I2C_DRIVER("IRQ_RXTHRESH\n");
        clear_irq(I2C_INTR_STATE_RX_THRESHOLD_BIT);
        microkit_irq_ack(ch);
        if (fsm_data.curr_state == S_CMD_RET) {
            fsm(&fsm_data);
        } else {
            LOG_I2C_DRIVER("Warning: received spurious RXTHRESH irq!\n");
        }
    // Error cases different IRQ for every fail type in Cheshire
    } else if (ch == IRQ_NAK_CH) {
        // In this version of opentitan, NACKs are delivered late and will double
        // up often. Ignore NACKs if we aren't expecting one
        i2c_halt();
        LOG_I2C_DRIVER("IRQ_NAK\n");
        clear_irq(I2C_INTR_STATE_NAK_BIT);
        microkit_irq_ack(ch);
        if (fsm_data.curr_state == S_CMD || fsm_data.curr_state == S_CMD_RET) {
            driver_data.err = I2C_ERR_NACK;
        }
    } else if (ch == IRQ_TIMEOUT_CH) {
        i2c_halt();
        LOG_I2C_DRIVER("IRQ_TIMEOUT\n");
        clear_irq(I2C_INTR_STATE_HOST_TIMEOUT_BIT);
        driver_data.err = I2C_ERR_TIMEOUT;
        microkit_irq_ack(ch);
    } else if (ch == IRQ_BAD_STOP_CH) {
        i2c_halt();
        LOG_I2C_DRIVER("IRQ_UNEXPECTED_STOP\n");
        clear_irq(I2C_INTR_STATE_UNEXP_STOP_BIT);
        driver_data.err = I2C_ERR_OTHER;
        microkit_irq_ack(ch);
    } else {
        microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }
    // Handle error IRQ if we are in the process of handling a request
    if (driver_data.err != I2C_ERR_OK && (fsm_data.curr_state == S_CMD || fsm_data.curr_state == S_CMD_RET)) {
        LOG_I2C_DRIVER("Transaction failed! Proceeding to respond.\n");
        i2c_halt();
        // We are outside the FSM - assign current state not next state.
        fsm_data.curr_state = S_RESPONSE;
        fsm_data.next_state = S_RESPONSE;
        fsm(&fsm_data);
    } else if (driver_data.err != I2C_ERR_OK) {
        LOG_I2C_DRIVER_ERR("Spurious error interrupt received! err=%u\n", driver_data.err);
        LOG_I2C_DRIVER_ERR("Current state: %s\n", state_to_str(fsm_data.curr_state));
        if (ch == IRQ_BAD_STOP_CH) LOG_I2C_DRIVER_ERR("IRQ_BAD_STOP\n");
        else if (ch == IRQ_TIMEOUT_CH) LOG_I2C_DRIVER_ERR("IRQ_TIMEOUT\n");
        else if (ch == IRQ_NAK_CH) LOG_I2C_DRIVER_ERR("IRQ_NAK\n");
        else LOG_I2C_DRIVER_ERR("No sane channel could have caused error! ch = %u\n", ch);
    }
}
