/*
 * Copyright 2023, UNSW
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
                            // another header at compile time, preferably via the makefile.

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("I2C DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif
#define LOG_DRIVER_ERR(...) do{ sddf_printf("I2C DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

/* sdfgen */
__attribute__((__section__(".i2c_driver_config"))) i2c_driver_config_t config;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

/* IRQs */
#define IRQ_FMTTHRESH_CH        (device_resources.irqs[0].id)
#define IRQ_RXTHRESH_CH         (device_resources.irqs[1].id)
#define IRQ_NAK_CH              (device_resources.irqs[2].id)
#define IRQ_BAD_STOP_CH         (device_resources.irqs[3].id)
#define IRQ_TIMEOUT_CH          (device_resources.irqs[4].id)

/* Transport */
i2c_queue_handle_t queue_handle;
uintptr_t request_region;
uintptr_t response_region;
uint8_t *slice;

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
                                      .t_low_min = (MAX(((T_HIGH_MIN) / (T_CLK)), 4)),
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
 * Clear bits causing controller halt in CONTROLLER_EVENTS. Causes I2C to resume functioning.
 */
static inline void i2c_reset_controller()
{
    // regs->controller_host_events = 0; //unused in cheshire!
    // TODO
}

static inline void load_timing_params(i2c_timing_params_t *p)
{
    // TIMING0
    // 0:12 -> T_H, 16:28 -> T_L
    uint32_t timing0 = (timing_params.t_h & I2C_TIMING0_THIGH_MASK)
                     | ((timing_params.t_l << I2C_TIMING0_TLOW_OFFSET) & I2C_TIMING0_TLOW_MASK);
    regs->timing0 = timing0;

    // TIMING1
    // 0:9 -> T_R, 16:24 -> T_F
    uint32_t timing1 = (timing_params.t_r & I2C_TIMING1_T_R_MASK)
                     | ((timing_params.t_f << I2C_TIMING1_T_F_OFFSET) & I2C_TIMING1_T_F_MASK);
    regs->timing1 = timing1;

    // TIMING2
    // 0:12 -> TSU_STA, 16:28 -> THD_STA
    /*uint32_t timing2 = (timing_params.t_hd_sta_min & I2C_TIMING2_TSU_STA_MASK)*/
    /*    | ((timing_params.t_su_sta_min << I2C_TIMING2_THD_STA_OFFSET) & I2C_TIMING2_THD_STA_MASK);*/
    int32_t timing2 = (timing_params.t_su_sta_min & I2C_TIMING2_TSU_STA_MASK)
                    | ((timing_params.t_hd_sta_min << I2C_TIMING2_THD_STA_OFFSET) & I2C_TIMING2_THD_STA_MASK);
    regs->timing2 = timing2;

    // TIMING3
    // 0:8 -> TSU_DAT, 16:28 -> THD_DAT
    uint32_t timing3 = (timing_params.t_su_dat_min & I2C_TIMING3_TSU_DAT_MASK)
                     | ((timing_params.t_hd_dat_min << I2C_TIMING3_THD_DAT_OFFSET) & I2C_TIMING3_THD_DAT_MASK);
    regs->timing3 = timing3;

    // TIMING4
    // 0:12 -> TSU_STO, 16:28 -> T_BUF
    uint32_t timing4 = (timing_params.t_sto_min & I2C_TIMING4_TSU_STO_MASK)
                     | ((timing_params.t_buf_min << I2C_TIMING4_T_BUF_OFFSET) & I2C_TIMING4_T_BUF_MASK);
    regs->timing4 = timing4;
}

void init(void)
{
    // Check sdfgen properties
    assert(i2c_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 4);
    assert(device_resources.num_regions == 1);

    regs = (volatile opentitan_i2c_regs_t *)device_resources.regions[0].region.vaddr;

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
    // Note: inequality appears backward here because the minimum period is actually the
    //       maximum speed. A lower period == a higher frequency. Hence, we check that
    //       f_h = (t_h^-1) < f_h_max since f = (t_h + t_l + t_f + t_r)^-1
    assert(timing_params.t_h <= timing_params.t_high_min);
    assert(timing_params.t_l <= timing_params.t_low_min);

    // Load timing parameters into registers
    load_timing_params(&timing_params);

    // Set up control register -> enable host mode, no other action for now.
    regs->ctrl |= I2C_CTRL_ENHOST_MASK;

    // Set up interrupts
    #ifndef I2C_CHESHIRE
    regs->intr_enable |= I2C_INTR_ENABLE_FMT_THRESHOLD_BIT;
    regs->intr_enable |= I2C_INTR_ENABLE_RX_THRESHOLD_BIT;
    regs->intr_enable |= I2C_INTR_ENABLE_CONTROLLER_HALT_BIT;
    regs->intr_enable |= I2C_INTR_ENABLE_CMD_COMPLETE_BIT;
    regs->intr_enable |= I2C_INTR_ENABLE_UNEXP_STOP_BIT;

    // Configure host FIFO
    regs->host_fifo_config |= (I2C_FMT_THRESHOLD)&I2C_HOST_FIFO_CONFIG_FMTTHRESH_MASK;
    regs->host_fifo_config |= (I2C_RX_THRESHOLD << I2C_HOST_FIFO_CONFIG_RXTHRESH_OFFSET) & I2C_HOST_FIFO_CONFIG_RXTHRESH_MASK;
    #endif

    // Prepare transport layer
    queue_handle = i2c_queue_init(config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr);
    i2c_reset_state(&driver_data);
    slice = NULL;
    LOG_DRIVER("Driver initialised.\n");
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
        LOG_DRIVER_ERR("Invalid fmt flags supplied to sddf_i2c_write! Combination cannot be represented "
                       "by hardware!");
        return -1;
    }
    uint32_t addr_fdata = (data)&I2C_FDATA_FBYTE_MASK;

    // Apply flags
    addr_fdata |= (flags->stop << I2C_FDATA_STOP_OFFSET) | (flags->rcont << I2C_FDATA_RCONT_OFFSET)
                | (flags->start << I2C_FDATA_START_OFFSET) | (flags->readb << I2C_FDATA_READB_OFFSET)
                | (flags->nakok << I2C_FDATA_NAKOK_OFFSET);

    regs->fdata = addr_fdata;
    return 0;
}

static inline uint32_t get_fmt_fifo_lvl(void)
{
    return regs->host_fifo_status & I2C_HOST_FIFO_STATUS_FMTLVL_MASK;
}

/**
 * If the CONTROLLER_HALT interrupt is asserted, find the error cause.
 */
static inline i2c_err_t i2c_get_error(void)
{
    #ifndef I2C_CHESHIRE
    //       possible that this version of opentitan just has no way to check for errors other than
    //       catching IRQs.
    uint32_t intr_state = i2c_mmio_read32(I2C_INTR_STATE);
    // Return first detected event in order of importance (same as bit order).
    if (intr_state & I2C_CONTROLLER_EVENTS_NACK_BIT) {
        LOG_DRIVER_ERR("Transaction failed! Device sent unexpected NACK.");
        return I2C_ERR_NACK;
    }
    if (intr_state & I2C_CONTROLLER_EVENTS_UNHANDLED_NACK_TIMEOUT_BIT) {
        LOG_DRIVER_ERR("Transaction failed! NACK timeout threshold reached.");
        return I2C_ERR_TIMEOUT;
    }
    if (intr_state & I2C_CONTROLLER_EVENTS_BUS_TIMEOUT_BIT) {
        LOG_DRIVER_ERR("Transaction failed! Bus timeout.");
        return I2C_ERR_TIMEOUT;
    }
    if (intr_state & I2C_CONTROLLER_EVENTS_ARBITRATION_LOST_BIT) {
        LOG_DRIVER_ERR("Transaction failed! Lost arbitration to another host!");
        return I2C_ERR_OTHER;
    }
    #endif
    return I2C_ERR_OK;
}

void state_cmd(fsm_data_t *fsm, i2c_driver_data_t *data, i2c_queue_handle_t *queue_handle)
{
    LOG_DRIVER("S_CMD entry\n");

    i2c_cmd_t cmd = data->active_cmd;
    bool work_done = false;

    // The following code loops through all available space in the registers there is either:
    // a. no space in a needed register (just FMT fifo in this case)
    // b. the command is over
    while (get_fmt_fifo_lvl() < OPENTITAN_I2C_FIFO_DEPTH && data->rw_idx < data->active_cmd.data_len) {
        fdata_fmt_flags_t flags = { 0, 0, 0, 0, 0 };
        uint8_t fmt_byte = 0;

        THREAD_MEMORY_ACQUIRE();
        // Handle sending start condition
        if (data->await_start) {
            LOG_DRIVER("Selected START\n");
            flags.start = 1;
            data->await_start = false;
        }

        // Handle sending write of sub address for register reads (WRRD flag)
        if (data->await_wrrd) {
            // Write-read/addr works differently on this platform than token-based ones.
            // There's no explicit addressing operation, we instead need to just write
            // the address and read bit
            LOG_DRIVER("Selecting WRRD\n");

            // Steps completed sequentially
            // 1. Write address
            if (data->await_wrrd == WRRD_WRADDR) {
                // Make fmt op: write address byte, leaving read bit as zero
                fmt_byte = i2c_curr_addr(data) & 0x7;
                data->await_wrrd--;
            // 2. Write subaddress
            } else if (data->await_wrrd == WRRD_SUBADDR) {
                // Make fmt op: write sub-address byte
                fmt_byte = cmd.payload.data[0];
                flags.readb = 0;
                data->await_wrrd = 0;   // We don't need to resend the start condition on this platform
                // Always reset await_start - can't switch back to read otherwise
                data->await_start = true;
            }

        } else if (data->await_addr) {
            LOG_DRIVER("Selected ADDR ... read = %d\n", cmd_is_read(cmd));

            // Write address and read bit
            fmt_byte = (i2c_curr_addr(data) & 0x7) | ((cmd_is_read(cmd) != 0) << 7);
            data->await_addr = false;

        // Handle writing data
        } else {
            LOG_DRIVER("Resuming in-progress read/write. rd=%d remaining=%d\n", cmd_is_read(cmd),
                       cmd.data_len - data->rw_idx);
            if (cmd_is_read(cmd)) {
                // Reads replace data byte with an integer of bytes to read
                flags.readb = 1;
                fmt_byte = MIN(cmd.data_len - data->rw_idx, OPENTITAN_I2C_READ_MAX);
                data->rw_idx += fmt_byte;
                assert(data->rw_idx <= cmd.data_len);
                // Always set continuing read unless this is the final read of this command
                flags.rcont = !((data->rw_idx < cmd.data_len));
            } else {
                // Writes insert a single byte to write
                fmt_byte = cmd.payload.data[data->rw_idx];
                data->rw_idx++;
            }

            // Send stop if needed (this is last op of command)
            if (data->await_stop && data->rw_idx == cmd.data_len) {
                flags.stop = 1;
                data->await_stop = 0;
            }
        }

        i2c_fmt_write(fmt_byte, &flags);
        // Important to include this - writing to the FMT needs to happen exactly above
        // because the write succeeding starts the hardware working.
        THREAD_MEMORY_RELEASE();
        work_done = true;
    }
    // Only await command response if we managed to do something. In the event that the FMT
    // fifo had no room, we need to go to sleep until there is room and try again.
    if (work_done) {
        fsm->next_state = S_CMD_RET;
    } else {
        LOG_DRIVER_ERR("Warning: S_CMD exited without progress! Sleeping to retry.");
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
    // Extract read data as long as we should have something here
    while (cmd_is_read(data->active_cmd) && rx_fifo_not_empty()) {
        // Get bytes_read amount of read data,copy data into return buffer
        uint8_t value = regs->rdata & 0xFF; // Bytes in low 8 of rdata register.
        LOG_DRIVER("loading into slice at %d value 0x%x (0x%p)\n", data->bytes_read, value,
                   &slice[data->bytes_read]);
        slice[data->bytes_read] = value;
        data->bytes_read++;
    }
    // Case 1: command fully complete
    if (data->rw_idx >= data->active_cmd.data_len) {
        f->next_state = S_SEL_CMD;
        f->yield = false;
    // Case 2: awaiting read return
    } else if (cmd_is_read(data->active_cmd) && data->bytes_read < data->rw_idx) {
        // Go to sleep until next IRQ (more rx data)
        f->next_state = S_CMD_RET;
        f->yield = true; //
    // Case 3: no more work to do here, but command is incomplete
    } else {
        f->next_state = S_CMD;
        f->yield = false;
    }
    LOG_DRIVER("No error. Bytes read = %u / %u dispatched for command\n", data->bytes_read, data->rd_idx);
}

/**
 * Reset the FIFOs and control register. Shouldn't overwrite anything from `init`
 */
int i2c_halt(void)
{
    // Disable host
    regs->ctrl &= ~(I2C_CTRL_ENHOST_MASK << I2C_CTRL_ENHOST_OFFSET);

    // Reset FMT and RX FIFOs
    regs->fifo_ctrl |= (I2C_FIFO_CTRL_FMTRST_MASK << I2C_FIFO_CTRL_FMTRST_OFFSET);
    regs->fifo_ctrl |= (I2C_FIFO_CTRL_RXRST_MASK << I2C_FIFO_CTRL_RXRST_OFFSET);

    // Re-enable host, waiting until disable has passed.
    while (regs->ctrl & (I2C_CTRL_ENHOST_MASK << I2C_CTRL_ENHOST_OFFSET)) {}
    regs->ctrl |= I2C_CTRL_ENHOST_MASK << I2C_CTRL_ENHOST_OFFSET;
    return 0;
}

void notified(microkit_channel ch)
{
    assert(driver_data.err == I2C_ERR_OK);
    if (ch == config.virt.id) {
        fsm_virt_notified(&fsm_data);
    } else if (ch == IRQ_FMTTHRESH_CH) {
        // Asserted when FMT FIFO has < 1 entry.
        LOG_DRIVER("IRQ_FMTTHRESH");

        // We can ignore this IRQ unless we are in S_CMD and awaiting commands to process
        // (i.e. the FMT FIFO was full last time we tried to push commands)
        if (fsm_data.curr_state == S_CMD) {
            fsm(&fsm_data);
        }
        microkit_irq_ack(ch);
    } else if (ch == IRQ_RXTHRESH_CH) {
        // Asserted when RX FIFO has > 0 entries.
        LOG_DRIVER("IRQ_RXTHRESH");
        if (fsm_data.curr_state == S_CMD_RET) {
            fsm(&fsm_data);
        } else {
            // If we're seeing this, our state machine is broken (probably).
            LOG_DRIVER_ERR("Warning) { received spurious RXTHRESH irq!\n");
        }
        microkit_irq_ack(ch);
    // Error cases different IRQ for every fail type in Cheshire
    } else if (ch == IRQ_NAK_CH) {
        driver_data.err = I2C_ERR_NACK;
        microkit_irq_ack(ch);
    } else if (ch == IRQ_TIMEOUT_CH) {
        driver_data.err = I2C_ERR_TIMEOUT;
        microkit_irq_ack(ch);
    } else if (ch == IRQ_BAD_STOP_CH) {
        driver_data.err = I2C_ERR_OTHER;
        microkit_irq_ack(ch);
    } else {
        microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }
    // Handle error IRQ
    if (driver_data.err != I2C_ERR_OK) {
        // Transaction has failed! Reset, get error and respond
        i2c_halt();
        i2c_reset_state(&driver_data);
        fsm_data.next_state = S_RESPONSE;
        fsm(&fsm_data);
    }
}
