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
#include "driver.h"
#include <sddf/i2c/i2c_driver.h>

#ifndef I2C_BUS_NUM
#error "I2C_BUS_NUM must be defined!"
#endif

// #define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("I2C DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_dprintf("I2C DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

struct i2c_regs {
    uint32_t ctl;           // control register
    uint32_t addr;          // slave address and other fields
    uint32_t tk_list0;      // where to put the meson i2c instructions (4 bits long)
    uint32_t tk_list1;      // where to put the meson i2c instructions (4 bits long)
    uint32_t wdata0;        // where to put the write payload from supplied buffer
    uint32_t wdata1;        // where to put the write payload from supplied buffer
    uint32_t rdata0;        // where read data gets put for a response by i2c
    uint32_t rdata1;        // where read data gets put for a response by i2c
};

__attribute__((__section__(".i2c_driver_config"))) i2c_driver_config_t config;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

// Hardware memory
uintptr_t clk_regs = 0x30000000;
uintptr_t gpio_regs = 0x30100000;

volatile struct i2c_regs *regs;

// Driver state for each interface
static i2c_driver_data_t driver_data;

// Shared memory regions
i2c_queue_handle_t queue_handle;
uint8_t *slice_region;

char *meson_token_to_str(uint8_t token)
{
    switch (token) {
    case MESON_I2C_TOKEN_END:
        return "MESON_I2C_TOKEN_END";
    case MESON_I2C_TOKEN_START:
        return "MESON_I2C_TOKEN_START";
    case MESON_I2C_TOKEN_ADDR_WRITE:
        return "MESON_I2C_TOKEN_ADDR_WRITE";
    case MESON_I2C_TOKEN_ADDR_READ:
        return "MESON_I2C_TOKEN_ADDR_READ";
    case MESON_I2C_TOKEN_DATA:
        return "MESON_I2C_TOKEN_DATA";
    case MESON_I2C_TOKEN_DATA_END:
        return "MESON_I2C_TOKEN_DATA_END";
    case MESON_I2C_TOKEN_STOP:
        return "MESON_I2C_TOKEN_STOP";
    default:
        return "Unknown token!";
    }
}

static inline char *state_to_str(i2c_state_t s)
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
        return "S_INVALID!";
    }
}

static inline char *i2c_err_to_str(i2c_err_t err)
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

/**
 * Prints the registers of the i2c interface
 */
static inline void i2c_dump(void)
{
// This makes actually debugging the driver impossible, so it's a separate #define.
#ifdef DEBUG_DRIVERRRR
    LOG_DRIVER("dumping interface state...\n");

    // Print control register fields
    // uint8_t ctl_man = (ctl & REG_CTRL_MANUAL) ? 1 : 0;
    uint8_t ctl_rd_cnt = ((regs->ctl & REG_CTRL_RD_CNT) >> 8);
    uint8_t ctl_curr_tk = ((regs->ctl & REG_CTRL_CURR_TK) >> 4);
    uint8_t ctl_err = (regs->ctl & REG_CTRL_ERROR) ? 1 : 0;
    uint8_t ctl_status = (regs->ctl & REG_CTRL_STATUS) ? 1 : 0;
    uint8_t ctl_start = (regs->ctl & REG_CTRL_START) ? 1 : 0;
    LOG_DRIVER("\t Control register:\n");
    LOG_DRIVER("\t\t Start: %u\n", ctl_start);
    LOG_DRIVER("\t\t Status: %u\n", ctl_status);
    LOG_DRIVER("\t\t Error: %u\n", ctl_err);
    LOG_DRIVER("\t\t Current token: %u\n", ctl_curr_tk);
    LOG_DRIVER("\t\t Read count: %u\n", ctl_rd_cnt);

    // Print address
    LOG_DRIVER("\t Address register: 0x%x\n", (regs->addr >> 1) & 0x7F);

    // Print token register 0 tokens
    LOG_DRIVER("\t Token register 0:\n");
    for (int i = 0; i < 8; i++) {
        uint8_t tk = (regs->tk_list0 >> (i * 4)) & 0xF;
        LOG_DRIVER("\t\t Token %d: %s\n", i, meson_token_to_str(tk));
    }

    // Print token register 1 tokens
    LOG_DRIVER("\t Token register 1:\n");
    for (int i = 0; i < 8; i++) {
        uint8_t tk = (regs->tk_list1 >> (i * 4)) & 0xF;
        LOG_DRIVER("\t\t Token %d: %s\n", i, meson_token_to_str(tk));
    }

    // Print wdata register 0 tokens
    LOG_DRIVER("\t Write data register 0:\n");
    for (int i = 0; i < 4; i++) {
        uint8_t tk = (regs->wdata0 >> (i * 8)) & 0xFF;
        LOG_DRIVER("\t\t Data %d: 0x%lx\n", i, tk);
    }

    // Print wdata register 1 tokens
    LOG_DRIVER("\t Write data register 1:\n");
    for (int i = 0; i < 4; i++) {
        uint8_t tk = (regs->wdata1 >> (i * 8)) & 0xFF;
        LOG_DRIVER("\t\t Data %d: 0x%lx\n", i, tk);
    }

    // Print rdata register 0
    LOG_DRIVER("\t Read data register 0:\n");
    for (int i = 0; i < 4; i++) {
        uint8_t tk = (regs->rdata0 >> (i * 8)) & 0xFF;
        LOG_DRIVER("\t\t Data %d: 0x%lx\n", i, tk);
    }

    // Print rdata register 1
    LOG_DRIVER("\t Read data register 1:\n");
    for (int i = 0; i < 4; i++) {
        uint8_t tk = (regs->rdata1 >> (i * 8)) & 0xFF;
        LOG_DRIVER("\t\t Data %d: 0x%lx\n", i, tk);
    }
#endif /* DEBUG_DRIVER */
}

/**
 * Initialise the i2c master interfaces.
*/
static inline void i2c_setup(void)
{
    LOG_DRIVER("initialising i2c master interfaces...\n");

    // Note: this is hacky - should do this using a GPIO driver.
    // Set up pinmux
    volatile uint32_t *gpio_mem = (void *)(gpio_regs + GPIO_OFFSET);

    volatile uint32_t *pinmux5_ptr = ((void *)gpio_mem + GPIO_PINMUX_5 * 4);
    // volatile uint32_t *pinmuxE_ptr      = ((void*)gpio_mem + GPIO_PINMUX_E*4);
    volatile uint32_t *pad_ds2b_ptr = ((void *)gpio_mem + GPIO_DS_2B * 4);
    // volatile uint32_t *pad_ds5a_ptr     = ((void*)gpio_mem + GPIO_DS_5A*4);
    volatile uint32_t *pad_bias2_ptr = ((void *)gpio_mem + GPIO_BIAS_2_EN * 4);
    // volatile uint32_t *pad_bias5_ptr    = ((void*)gpio_mem + GPIO_BIAS_5_EN*4);
    volatile uint32_t *clk81_ptr = ((void *)clk_regs + I2C_CLK_OFFSET);

    // Read existing register values
    uint32_t pinmux5 = *pinmux5_ptr;
    // uint32_t pinmuxE = *pinmuxE_ptr;
    uint32_t clk81 = *clk81_ptr;

    // Common values
    const uint8_t ds = 3;    // 3 mA
    uint8_t pinfunc;

#if I2C_BUS_NUM == 2
    // Enable i2cm2 -> pinmux 5
    LOG_DRIVER("bus 2 initialising\n");
    pinfunc = GPIO_PM5_X_I2C;
    pinmux5 |= (pinfunc << 4) | (pinfunc << 8);
    *pinmux5_ptr = pinmux5;

    // Check that registers actually changed
    if (!(*pinmux5_ptr & (GPIO_PM5_X18 | GPIO_PM5_X17))) {
        LOG_DRIVER_ERR("failed to set pinmux5!\n");
    }

    // Set GPIO drive strength
    *pad_ds2b_ptr &= ~(GPIO_DS_2B_X17 | GPIO_DS_2B_X18);
    *pad_ds2b_ptr |= ((ds << GPIO_DS_2B_X17_SHIFT) | (ds << GPIO_DS_2B_X18_SHIFT));

    // Check register updated
    if ((*pad_ds2b_ptr & (GPIO_DS_2B_X17 | GPIO_DS_2B_X18))
        != ((ds << GPIO_DS_2B_X17_SHIFT) | (ds << GPIO_DS_2B_X18_SHIFT))) {
        LOG_DRIVER_ERR("failed to set drive strength for m2!\n");
    }

    // Disable bias, because the odroid i2c hardware has undocumented internal ones
    *pad_bias2_ptr &= ~((1 << 18) | (1 << 17)); // Disable m2 bias - x17 and x18

    // Check registers updated
    if ((*pad_bias2_ptr & ((1 << 18) | (1 << 17))) != 0) {
        LOG_DRIVER_ERR("failed to disable bias for m2!\n");
    }
#elif I2C_BUS_NUM == 3
    // Enable i2cm3 -> pinmux E
    pinfunc = GPIO_PE_A_I2C;
    pinmuxE |= (pinfunc << 24) | (pinfunc << 28);
    *pinmuxE_ptr = pinmuxE;

    // Check registers actually changed
    if (!(*pinmuxE_ptr & (GPIO_PE_A15 | GPIO_PE_A14))) {
        LOG_DRIVER_ERR("failed to set pinmuxE!\n");
    }

    // Set GPIO drive strength
    *pad_ds5a_ptr &= ~(GPIO_DS_5A_A14 | GPIO_DS_5A_A15);
    *pad_ds5a_ptr |= ((ds << GPIO_DS_5A_A14_SHIFT) | (ds << GPIO_DS_5A_A15_SHIFT));

    // Check register updated
    if ((*pad_ds5a_ptr & (GPIO_DS_5A_A14 | GPIO_DS_5A_A15))
        != ((ds << GPIO_DS_5A_A14_SHIFT) | (ds << GPIO_DS_5A_A15_SHIFT))) {
        LOG_DRIVER_ERR("failed to set drive strength for m3!\n");
    }

    // Disable bias, because the odroid i2c hardware has undocumented internal ones
    *pad_bias5_ptr &= ~((1 << 14) | (1 << 15)); // Disable m3 bias - a14 and a15

    // Check registers updated
    if ((*pad_bias5_ptr & ((1 << 14) | (1 << 15))) != 0) {
        LOG_DRIVER_ERR("failed to disable bias for m3!\n");
    }
#endif /* I2C_BUS_NUM */

    // Enable i2c by removing clock gate
    clk81 |= (I2C_CLK81_BIT);
    *clk81_ptr = clk81;

    // Check that registers actually changed
    if (!(*clk81_ptr & I2C_CLK81_BIT)) {
        LOG_DRIVER_ERR("failed to toggle clock!\n");
    }

    // Initialise fields
    regs->ctl &= ~(REG_CTRL_MANUAL);       // Disable manual mode
    regs->ctl &= ~(REG_CTRL_ACK_IGNORE);   // Disable ACK IGNORE
    regs->ctl |= (REG_CTRL_CNTL_JIC);      // Bypass dynamic clock gating

    // Handle clocking
    // (comment) Stolen from Linux Kernel's amlogic driver
    /*
    * According to I2C-BUS Spec 2.1, in FAST-MODE, LOW period should be at
    * least 1.3uS, and HIGH period should be at lease 0.6. HIGH to LOW
    * ratio as 2 to 5 is more safe.
    * Duty  = H/(H + L) = 2/5   -- duty 40%%   H/L = 2/3
    * Fast Mode : 400k
    * High Mode : 3400k
    */
    // const uint32_t clk_rate = 166666666; // 166.666MHz -> clk81
    // const uint32_t freq = 400000; // 400kHz
    // const uint32_t delay_adjust = 0;
    // uint32_t div_temp = (clk_rate * 2)/(freq * 5);
    // uint32_t div_h = div_temp - delay_adjust;
    // uint32_t div_l = (clk_rate * 3)/(freq * 10);

    // Duty cycle slightly high with this - should adjust (47% instead of 40%)
    // TODO: add clock driver logic here to dynamically set speed. This is a hack.
    //       The below values allow us to be a spec compliant 400KHz controller w/
    //       duty cycle, and high/low time appropriate
    uint32_t div_h = 154;
    uint32_t div_l = 116;

    // Set clock divider
    regs->ctl &= ~(REG_CTRL_CLKDIV_MASK);
    regs->ctl |= (div_h << REG_CTRL_CLKDIV_SHIFT);

    // Set SCL filtering
    regs->addr &= ~(REG_ADDR_SCLFILTER);
    regs->addr |= (0x0 << 11);

    // Set SDA filtering
    regs->addr &= ~(REG_ADDR_SDAFILTER);
    regs->addr |= (0x0 << 8);

    // Set clock delay levels
    // Field has 9 bits: clear then shift in div_l
    regs->addr &= ~(0x1FF << REG_ADDR_SCLDELAY_SHFT);
    regs->addr |= (div_l << REG_ADDR_SCLDELAY_SHFT);

    // Enable low delay time adjustment
    regs->addr |= REG_ADDR_SCLDELAY_ENABLE;
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
 * Restarts the list processor
 */
static inline int i2c_start(void)
{
    LOG_DRIVER("LIST PROCESSOR START\n");
    regs->ctl &= ~0x1;
    regs->ctl |= 0x1;
    if (!(regs->ctl & 0x1)) {
        LOG_DRIVER("failed to set start bit!\n");
        return -1;
    }
    return 0;
}

/**
 * Aborts the current operation by generating an I2C STOP command on the I2C bus
 */
static inline int i2c_halt(void)
{
    LOG_DRIVER("LIST PROCESSOR HALT\n");
    regs->ctl &= ~0x1;
    if ((regs->ctl & 0x1)) {
        LOG_DRIVER("failed to halt!\n");
        return -1;
    }
    return 0;
}

/**
 * Return TRUE if current command is a read operation, irrespective of WRRD ops.
 */
static inline bool cmd_is_read(i2c_cmd_t c)
{
    return c.flag_mask & I2C_FLAG_READ;
}

/**
 * Return TRUE if current token corresponds to a read, else FALSE.
 * This function exists to handle correctly sending the WRRD write.
 */
static inline bool data_direction_rd(i2c_driver_data_t *data)
{
    return cmd_is_read(*data->active_cmd) & !data->await_wrrd;
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
    slice_region = NULL;

    microkit_dbg_puts("Driver initialised.\n");
}

/**
 * S_IDLE
 * Reset driver data and goto request state if there's work to do. Otherwise, go to sleep.
 *
 * Succeeds: S_RESP, or any state when failing
 * Sucessor(s): S_REQ
 */
void state_idle(fsm_data_t *fsm, i2c_driver_data_t *data)
{
    LOG_DRIVER("S_IDLE entry\n");
    i2c_reset_state(data);
    if (!i2c_queue_empty(queue_handle.request->ctrl)) {
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
 * Take a new request from the queue.
 *
 * Succeeds: S_IDLE
 * Successor(s): S_SEL_CMD (success), S_IDLE (fail)
 */
void state_req(fsm_data_t *fsm, i2c_driver_data_t *data)
{
    // Pre-emptively set S_IDLE as next state in case any of the error checks fail.
    fsm->next_state = S_IDLE;

    // Sanity check. This should be impossible.
    if (i2c_queue_empty(queue_handle.request->ctrl)) {
        LOG_DRIVER_ERR("State machine reached invalid state! In request state without work to do...");
        return;
    }

    // Get request from queue
    // Otherwise, begin work. Start by extracting the request
    i2c_addr_t bus_address = 0;
    uintptr_t slice_region_vaddr, command_region_vaddr;
    uint16_t size = 0;
    int err = i2c_dequeue_request(queue_handle, &bus_address, &command_region_vaddr, &slice_region_vaddr, &size);
    LOG_DRIVER("New request: data->%p\n", (void *)(command_region_vaddr));
    if (err) {
        LOG_DRIVER_ERR("fatal: failed to dequeue request\n");
        return;
    }
    if (size > I2C_MAX_DATA_SIZE) {
        LOG_DRIVER_ERR("Invalid request size: %u!\n", size);
        return;
    }
    if (bus_address > MESON_I2C_MAX_BUS_ADDRESS) {
        LOG_DRIVER_ERR("attempted to write to address > 7-bit range!\n");
        return;
    }
    LOG_DRIVER("Loading request for bus address 0x%x\n", (unsigned int)(bus_address));

    // Virt converts address given by
    data->curr_command_region = (i2c_cmd_t *)command_region_vaddr;
    data->slice_base = slice_region_vaddr;
    data->addr = bus_address;
    data->curr_request_len = size;
    fsm->next_state = S_SEL_CMD;
    return;
}

/**
 * S_SEL_CMD (command)
 * Process all components of the request selected by S_REQ, pick a command to operate on.
 * This sets up the await flags and rw_idx, as well as keeping track of progression through
 * the buffer. It also decides when the request is finished.
 * Succeeds: S_REQ, S_CMD_RET
 * Sucessor(s): S_CMD, S_IDLE (fatal), S_RESPONSE (done or error)
 */
void state_sel_cmd(fsm_data_t *fsm, i2c_driver_data_t *data)
{
    // If we're in this state, we know that either:
    // a. There's no active command (just started)
    // b. The previous command finished.
    // We must decide on the next command, or retire to S_RESP

    // Get next command
    if (data->req_idx < data->curr_request_len) {
        LOG_DRIVER("Accepting new cmd...\n");
        i2c_cmd_t cmd = data->curr_command_region[data->req_idx];
        i2c_cmd_t old_cmd = data->active_cmd == NULL ? cmd : *data->active_cmd;
        if (cmd.flag_mask & I2C_FLAG_RSTART && (cmd_is_read(cmd) != cmd_is_read(old_cmd))) {
            LOG_DRIVER_ERR("Invalid command sequence! Cannot `I2C_FLAG_RSTART` without "
                           "matching data direction! Invalid cmd dropped...");
            data->err = I2C_ERR_BADSEQ;
            fsm->next_state = S_RESPONSE;
            return;
        }
        // Set interface state
        data->await_start = true;    // We can never skip starting!
        data->await_addr = !(cmd.flag_mask & I2C_FLAG_RSTART); // Don't send address if
                                                               // this is a repeat start
        // Set write-read counter if needed. Ignore WRRD if writing because it has no effect.
        data->await_wrrd = (cmd.flag_mask & I2C_FLAG_WRRD) && (cmd.flag_mask & I2C_FLAG_READ) ? NUM_WRRD_STEPS : 0;
        data->await_stop = cmd.flag_mask & I2C_FLAG_STOP;
        data->rw_idx = 0;
        data->active_cmd = &data->curr_command_region[data->req_idx];

        LOG_DRIVER("## Command loaded (SEL_CMD) ##\n");
        LOG_DRIVER("\t len = %u\n", cmd.len);
        LOG_DRIVER("\t slice_region offset = %zu\n", cmd.offset);
        LOG_DRIVER("\t FLAG_READ: %u\n", (cmd.flag_mask & I2C_FLAG_READ) != 0);
        LOG_DRIVER("\t FLAG_WRRD: %u\n", (cmd.flag_mask & I2C_FLAG_WRRD) != 0);
        LOG_DRIVER("\t FLAG_STOP: %u\n", (cmd.flag_mask & I2C_FLAG_STOP) != 0);
        LOG_DRIVER("\t FLAG_RSTART: %u\n", (cmd.flag_mask & I2C_FLAG_RSTART) != 0);

        // Increment req idx for next time
        data->req_idx++;
        if (data->req_idx == data->curr_request_len - 1)
            LOG_DRIVER("Handling last cmd of request...\n");
        if (!data->err)
            fsm->next_state = S_CMD;
        else
            fsm->next_state = S_RESPONSE;  // If there's an error, give up on cmd entirely.
    } else {
        LOG_DRIVER("Request finished!\n");
        fsm->next_state = S_RESPONSE;
    }
    return;
}

void state_cmd(fsm_data_t *fsm, i2c_driver_data_t *data)
{
    LOG_DRIVER("S_CMD entry\n");
    // Load address into address register
    // Address goes into low 7 bits of address register
    // First clear all address bits (bits 0:7 inclusive)
    regs->addr &= ~(0xff);
    // Device expects that the 7-bit address is shifted left by 1 bit
    regs->addr |= ((data->addr & 0x7f) << 1);
    LOG_DRIVER("\t Address register: 0x%x\n", (regs->addr >> 1) & 0x7F);
    LOG_DRIVER("\t Should match data->addr = %x\n", data->addr);

    i2c_cmd_t cmd = *data->active_cmd;
    // Clear token buffer registers
    regs->tk_list0 = 0x0;
    regs->tk_list1 = 0x0;
    regs->wdata0 = 0x0;
    regs->wdata1 = 0x0;

    // Offset into token list registers
    uint32_t tk_offset = 0;
    // Offset into wdata registers
    uint32_t wdata_offset = 0;
    // Offset into rdata registers
    uint32_t rdata_offset = 0;

    // The following code loops through all available space in the registers their is either:
    // a. no space in a needed register
    // b. the command is over
    // - add meson_token equivalent to token list register
    // - if read or write increment wdata or rdata offset
    // - if write add buffer data into wdata
    // Note: we check <= instead of < for the cmd length because we always need an extra round to
    //       send a STOP token.
    while (tk_offset < 16 && wdata_offset < 8 && rdata_offset < 8 && data->rw_idx <= data->active_cmd->len) {
        /*LOG_DRIVER("request_data_offset : 0x%lx, tk_offset: 0x%lx, wdata_offset: 0x%lx, rdata_offset: 0x%lx\n",*/
        /*           request_data_offset, tk_offset, wdata_offset, rdata_offset);*/
        /**/
        // Discover next operation
        uint8_t meson_token;
        uint32_t payload_byte;
        slice_region = (uint8_t *)(data->slice_base + cmd.offset);

        // Handle sending start condition
        if (data->await_start) {
            LOG_DRIVER("Selected START\n");
            meson_token = MESON_I2C_TOKEN_START;
            data->await_start = false;

            // Handle sending write of sub address for register reads (WRRD flag)
        } else if (data->await_wrrd) {
            LOG_DRIVER("Selecting WRRD\n");
            // If we're on NUM_WRRD_STEPS, we've just sent the WRITE token. Next item: send
            // subaddress byte.
            if (data->await_wrrd == NUM_WRRD_STEPS) {
                // Send preliminary write
                LOG_DRIVER("WRRD: sending address write...\n");
                meson_token = MESON_I2C_TOKEN_ADDR_WRITE;
            } else if (data->await_wrrd == 2) {
                LOG_DRIVER("WRRD: sending address byte %u\n", slice_region[0]);
                // Send address of register
                meson_token = MESON_I2C_TOKEN_DATA;
                payload_byte = slice_region[0]; // Address of reg always contained in 0th byte
                    // of read buffer.
            } else {
                meson_token = MESON_I2C_TOKEN_START;
            }
            data->await_wrrd--;

            // Handle sending address token
        } else if (data->await_addr) {
            meson_token = cmd_is_read(cmd) ? MESON_I2C_TOKEN_ADDR_READ : MESON_I2C_TOKEN_ADDR_WRITE;
            LOG_DRIVER("Selected ADDR ... read = %d\n", cmd_is_read(cmd));
            data->await_addr = false;

            // Handle sending stop condition once command has sent all bytes if we need one.
            // NOTE: possible missing condition?
        } else if (data->rw_idx >= cmd.len) {
            if (data->await_stop) {
                LOG_DRIVER("Selected STOP\n");
                meson_token = MESON_I2C_TOKEN_STOP;
                data->await_stop = false;
            } else {
                // If we don't need a stop condition, skip final loop.
                break;
            }
            data->rw_idx++; // Hacky, but saves keeping an extra variable to track
                // stop condition between here and S_CMD_RET

            // Handle data transmission
        } else {
            LOG_DRIVER("Resuming in-progress read/write. rd=%d remaining=%d\n", cmd_is_read(cmd),
                       data->active_cmd->len - data->rw_idx);

            // We are in the middle of a read or write. Pick up where we left off
            if (data->rw_idx == (cmd.len - 1) && cmd_is_read(cmd)) {
                // Write data end on last byte of a read.
                meson_token = MESON_I2C_TOKEN_DATA_END;
            } else {
                assert(data->rw_idx < cmd.len);
                meson_token = MESON_I2C_TOKEN_DATA;
            }
            // If writing, and this is not the subaddress of a WRRD
            if (!cmd_is_read(cmd)) {
                payload_byte = slice_region[data->rw_idx]; // Take next byte to write
            }
            data->rw_idx++;
        }

        /*LOG_DRIVER("meson_token: 0x%lx, request_data_offset : 0x%lx, tk_offset: 0x%lx, wdata_offset: 0x%lx, rdata_offset: 0x%lx\n",*/
        /*           meson_token, request_data_offset, tk_offset, wdata_offset, rdata_offset);*/

        if (tk_offset < 8) {
            regs->tk_list0 |= (meson_token << (tk_offset * 4));
        } else {
            regs->tk_list1 |= (meson_token << ((tk_offset % 8) * 4));
        }
        tk_offset++;

        // If data token and we are writing (inc. WRRD), load data into wbuf registers
        if (meson_token == MESON_I2C_TOKEN_DATA && !data_direction_rd(data)) {
            if (wdata_offset < 4) {
                regs->wdata0 |= (payload_byte << (wdata_offset * 8));
            } else {
                regs->wdata1 |= (payload_byte << ((wdata_offset - 4) * 8));
            }
            LOG_DRIVER("\tInjecting write payload: %x\n", payload_byte);
            wdata_offset++;
        }

        /* If data token and we are reading (not WRRD write), increment counter of rdata */
        if ((meson_token == MESON_I2C_TOKEN_DATA || meson_token == MESON_I2C_TOKEN_DATA_END)
            && data_direction_rd(data)) {
            // Note: rdata_offset just makes sure we don't read more than 8 times in
            //       a single transaction as this is the limit of the hardware.
            rdata_offset++;
        }
        LOG_DRIVER("\t\t->> selected %s ...\n", meson_token_to_str(meson_token));
    }
    LOG_DRIVER("Tokens loaded. %u cmds remain for this request\n", data->curr_request_len - data->req_idx);
    // Start list processor
    i2c_start();
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
void state_cmd_ret(fsm_data_t *f, i2c_driver_data_t *data)
{
    // Get result
    uint8_t curr_token = 0;
    uint8_t bytes_read = 0;
    bool write_error = i2c_get_error(&bytes_read, &curr_token);
    slice_region = (uint8_t *)(data->slice_base + data->active_cmd->offset);
    LOG_DRIVER("S_CMD_RET: returning with %u bytes read, halt token = %u\n", bytes_read, curr_token);

    // If there was an error, cancel the rest of this transaction and load the
    // error information into the return buffer.
    if (write_error) {
        // handle_response_timeout already has error logic for timeout
        if (curr_token == MESON_I2C_TOKEN_ADDR_READ) {
            data->err = I2C_ERR_NOREAD;
        } else {
            data->err = I2C_ERR_NACK;
        }
        LOG_DRIVER("token that caused error: %d!\n", curr_token);
        f->next_state = S_RESPONSE;

    } else {
        LOG_DRIVER("No error. Bytes read = %u\n", bytes_read);
        // Get bytes_read amount of read data,copy data into return buffer
        for (int i = 0; i < bytes_read; i++) {
            assert(cmd_is_read(*data->active_cmd)); // If we're here and we didn't read, die
            uint8_t value = 0;
            if (i < 4) {
                value = (regs->rdata0 >> (i * 8)) & 0xFF;
            } else if (i < 8) {
                value = (regs->rdata1 >> ((i - 4) * 8)) & 0xFF;
            }
            LOG_DRIVER("loading into slice_region at %d value 0x%x (0x%p)\n", data->bytes_read, value,
                       &slice_region[data->bytes_read]);
            slice_region[data->bytes_read] = value;
            data->bytes_read++;
        }
        // Decide whether this is the end or to return back to sel_cmd
        // Note: this isn't a signpost error. S_CMD runs for one round extra to send a STOP
        if (data->rw_idx > data->active_cmd->len)
            f->next_state = S_SEL_CMD;
        else
            f->next_state = S_CMD;
    }
}

/**
 * S_RESP
 * Handle returning current request to virt.
 *
 * Succeeds: S_SEL_CMD (success), any other state (err set)
 * Sucessor(s): S_IDLE
 */
void state_resp(fsm_data_t *f, i2c_driver_data_t *data)
{
    LOG_DRIVER("S_RESP entry\n");
    if (i2c_queue_full(queue_handle.response->ctrl)) {
        LOG_DRIVER_ERR("Tried to return a response, but no buffers are available! Dropping..\n");
        f->next_state = S_IDLE;
        i2c_halt();
        return;
    }

    // Handle failure
    int ret;
    if (data->err) {
        LOG_DRIVER("Request failed with error %s\n", i2c_err_to_str(data->err));
        ret = i2c_enqueue_response(queue_handle, data->addr, data->err, data->req_idx);
        i2c_halt();
    } else {
        LOG_DRIVER("Request returning with no error: address = %u, bytes_read = %u\n", data->addr, data->bytes_read);
        ret = i2c_enqueue_response(queue_handle, data->addr, data->err, 0);
    }
    f->next_state = S_IDLE;
    if (ret) {
        LOG_DRIVER_ERR("Failed to return response to virt!\n");
    }
    microkit_notify(config.virt.id);
}

fsm_data_t fsm_data = { 0, 0, 0 };

// This table is responsible for relating the state enum to the state functions.
// I.e. i2c_state_table[0] == i2c_state_table[S_IDLE] == state_idle(*f, *data).
// If you change the state enum and/or add/remove states, make sure you keep this up to date!
i2c_state_func_t *i2c_state_table[NUM_STATES] = { state_idle, state_req,     state_sel_cmd,
                                                  state_cmd,  state_cmd_ret, state_resp };

/**
 * I2C finite state machine. Abstracts stateful execution into fixed states to improve
 * maintainability (and save a little bit of room on the stack!). The FSM responds
 * to *internal* events principally, not Microkit events. As a result, we depend upon
 * state functions to declare when the PD should go to sleep by setting yield to true.
 */
void fsm(fsm_data_t *f)
{
    do {
        LOG_DRIVER("FSM: %s\n", state_to_str(f->curr_state));
        // Run current state
        i2c_state_table[f->curr_state](&fsm_data, &driver_data);
        f->curr_state = f->next_state;
        LOG_DRIVER("Next state: %s\n", state_to_str(f->next_state));
    } while (!f->yield);
    // Always reset the yield flag when the FSM gives up. Whenever this function
    // returns the PD should have gone to sleep.
    f->yield = false;
    LOG_DRIVER("FSM: yielding in state = %s\n", state_to_str(f->curr_state));
    return;
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
    LOG_DRIVER("Notified\n");
    if (ch == config.virt.id) {
        LOG_DRIVER("Notified by virt!\n");
        if (fsm_data.curr_state == S_IDLE)
            fsm(&fsm_data);
    } else if (ch == device_resources.irqs[0].id) {
        LOG_DRIVER("IRQ!\n");
        if (fsm_data.curr_state == S_CMD_RET) {
            fsm(&fsm_data);
        } else {
            LOG_DRIVER_ERR("Received spurious completion interrupt!\n");
        }
        microkit_irq_ack(ch);
    } else if (ch == device_resources.irqs[1].id) {
        /* Timeout IRQ */
        LOG_DRIVER("Timeout!\n");
        /*i2c_halt(); // Temporary!*/
        /*handle_response_timeout();  // TODO: handle*/
        microkit_irq_ack(ch);
    } else {
        LOG_DRIVER_ERR("unexpected notification on channel %d\n", ch);
    }
}
