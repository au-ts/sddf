/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Implementation of the i2c driver targeting the ODROID C4.
// Each instance of this driver corresponds to one of the four
// available i2c master interfaces on the device.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#include <microkit.h>
#include <sddf/i2c/queue.h>
#include "driver.h"

#ifndef I2C_BUS_NUM
#error "I2C_BUS_NUM must be defined!"
#endif

#define VIRTUALISER_CH 0
#define IRQ_CH 1
#define IRQ_TIMEOUT_CH 2

// #define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("I2C DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("I2C DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

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

// Hardware memory
uintptr_t gpio_regs;
uintptr_t clk_regs;
uintptr_t i2c_regs;

// Driver state for each interface
volatile i2c_ifState_t i2c_ifState;

i2c_queue_handle_t queue_handle;

uintptr_t request_region;
uintptr_t response_region;

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

/**
 * Prints the registers of the i2c interface
 */
static inline void i2c_dump(volatile struct i2c_regs *regs)
{
#ifdef DEBUG_DRIVER
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
static inline void i2c_setup()
{
    LOG_DRIVER("initialising i2c master interfaces...\n");

    volatile struct i2c_regs *regs = (volatile struct i2c_regs *) i2c_regs;

    // Note: this is hacky - should do this using a GPIO driver.
    // Set up pinmux
    volatile uint32_t *gpio_mem = (void *)(gpio_regs + GPIO_OFFSET);

    volatile uint32_t *pinmux5_ptr      = ((void *)gpio_mem + GPIO_PINMUX_5 * 4);
    // volatile uint32_t *pinmuxE_ptr      = ((void*)gpio_mem + GPIO_PINMUX_E*4);
    volatile uint32_t *pad_ds2b_ptr     = ((void *)gpio_mem + GPIO_DS_2B * 4);
    // volatile uint32_t *pad_ds5a_ptr     = ((void*)gpio_mem + GPIO_DS_5A*4);
    volatile uint32_t *pad_bias2_ptr    = ((void *)gpio_mem + GPIO_BIAS_2_EN * 4);
    // volatile uint32_t *pad_bias5_ptr    = ((void*)gpio_mem + GPIO_BIAS_5_EN*4);
    volatile uint32_t *clk81_ptr        = ((void *)clk_regs + I2C_CLK_OFFSET);

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
    *pad_ds2b_ptr |= ((ds << GPIO_DS_2B_X17_SHIFT) |
                      (ds << GPIO_DS_2B_X18_SHIFT));

    // Check register updated
    if ((*pad_ds2b_ptr & (GPIO_DS_2B_X17 | GPIO_DS_2B_X18)) != ((ds << GPIO_DS_2B_X17_SHIFT) |
                                                                (ds << GPIO_DS_2B_X18_SHIFT))) {
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
    *pad_ds5a_ptr |= ((ds << GPIO_DS_5A_A14_SHIFT) |
                      (ds << GPIO_DS_5A_A15_SHIFT));

    // Check register updated
    if ((*pad_ds5a_ptr & (GPIO_DS_5A_A14 | GPIO_DS_5A_A15)) != ((ds << GPIO_DS_5A_A14_SHIFT) |
                                                                (ds << GPIO_DS_5A_A15_SHIFT))) {
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
static inline bool i2c_get_error(volatile struct i2c_regs *regs, uint8_t *bytes_read, uint8_t *curr_token)
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
static inline int i2c_start(volatile struct i2c_regs *regs)
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
static inline int i2c_halt(volatile struct i2c_regs *regs)
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
 * Converts our token abstraction into meson compatible tokens
 */
static inline uint8_t i2c_token_convert(i2c_token_t token)
{
    switch (token) {
    case I2C_TOKEN_END:
        return MESON_I2C_TOKEN_END;
    case I2C_TOKEN_START:
        return MESON_I2C_TOKEN_START;
    case I2C_TOKEN_ADDR_WRITE:
        i2c_ifState.data_direction = DATA_DIRECTION_WRITE;
        return MESON_I2C_TOKEN_ADDR_WRITE;
    case I2C_TOKEN_ADDR_READ:
        i2c_ifState.data_direction = DATA_DIRECTION_READ;
        return MESON_I2C_TOKEN_ADDR_READ;
    case I2C_TOKEN_STOP:
        return MESON_I2C_TOKEN_STOP;
    default:
        LOG_DRIVER_ERR("invalid data token in request! \"0x%x\"\n", token);
        return -1;
    }
}

/**
 * Loads tokens onto specified i2c interface registers
 * This function resets interface registers before uploading data
 */
static inline void i2c_load_tokens(volatile struct i2c_regs *regs)
{
    LOG_DRIVER("starting token load\n");
    i2c_token_t *tokens = i2c_ifState.curr_data;
    LOG_DRIVER("Tokens remaining in this req: %zu\n", i2c_ifState.remaining);

    // Load address into address register
    // Address goes into low 7 bits of address register
    // First clear all address bits (bits 0:7 inclusive)
    regs->addr &= ~(0xff);
    // Device expects that the 7-bit address is shifted left by 1 bit
    regs->addr |= ((i2c_ifState.addr & 0x7f) << 1);

    LOG_DRIVER("regs->addr 0x%lx\n", regs->addr);

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

    // Offset into supplied buffer
    int request_data_offset = i2c_ifState.curr_request_len - i2c_ifState.remaining;

    // basically loops all available space in the registers until one has not more room or request is finished and in the process:
    // - add meson_token equivalent to token list register
    // - if read or write increment wdata or rdata offset
    // - if write add buffer data into wdata
    // It should be noted that we do not explicitly add the MESON_I2C_TOKEN_END to the token list register as
    // we have already cleared the registers and it has a value of zero.

    while (tk_offset < 16 && wdata_offset < 8 && rdata_offset < 8 && request_data_offset < i2c_ifState.curr_request_len) {
        LOG_DRIVER("request_data_offset : 0x%lx, tk_offset: 0x%lx, wdata_offset: 0x%lx, rdata_offset: 0x%lx\n",
                   request_data_offset, tk_offset, wdata_offset, rdata_offset);

        // Discover next operation
        uint8_t meson_token, data;
        if (i2c_ifState.rw_remaining == 0) {
            LOG_DRIVER("Accepting new token...\n");
            // Get meson_token if no read/write is in progress.
            meson_token = i2c_token_convert(tokens[request_data_offset]);

            // Grab buffer length, if appropriate.
            if (meson_token == MESON_I2C_TOKEN_ADDR_WRITE || meson_token == MESON_I2C_TOKEN_ADDR_READ) {
                LOG_DRIVER("Beginning RW operation!\n");
                // R/W buffer incoming: |RD/WR|LEN|DATA0|DATA1| ... |DATA[LEN-1]|
                uint8_t buff_length = tokens[request_data_offset + 1];

                // Set interface state
                i2c_ifState.rw_remaining = buff_length;
                i2c_ifState.data_direction = (meson_token == MESON_I2C_TOKEN_ADDR_WRITE)
                                             ? DATA_DIRECTION_WRITE : DATA_DIRECTION_READ;

                LOG_DRIVER("DD=%d    REM=%d\n", i2c_ifState.data_direction, i2c_ifState.rw_remaining);

                // IMPORTANT: skip buffer length byte!
                request_data_offset++;
            }

        } else {
            LOG_DRIVER("Resuming in-progress read/write. DD=%d remaining=%d\n",
                       i2c_ifState.data_direction, i2c_ifState.rw_remaining);
            // We are in the middle of a read or write. Pick up where we left off
            if (i2c_ifState.rw_remaining == 1 && i2c_ifState.data_direction == DATA_DIRECTION_READ) {
                // Write data end on last byte of a read.
                meson_token = MESON_I2C_TOKEN_DATA_END;
                // TODO: @mattr potential fencepost error? Seems correct to me though.
            } else {
                meson_token = MESON_I2C_TOKEN_DATA;
            }
            if (i2c_ifState.data_direction == DATA_DIRECTION_WRITE) {
                data = tokens[request_data_offset]; // Take next byte to write
            }
            LOG_DRIVER("DATA=%u\n", data);
            i2c_ifState.rw_remaining--;
        }



        LOG_DRIVER("meson_token: 0x%lx, request_data_offset : 0x%lx, tk_offset: 0x%lx, wdata_offset: 0x%lx, rdata_offset: 0x%lx\n",
                   meson_token, request_data_offset, tk_offset, wdata_offset, rdata_offset);


        if (tk_offset < 8) {
            regs->tk_list0 |= (meson_token << (tk_offset * 4));
        } else {
            regs->tk_list1 |= (meson_token << ((tk_offset % 8) * 4));
        }
        tk_offset++;

        // If data token and we are writing, load data into wbuf registers
        if (meson_token == MESON_I2C_TOKEN_DATA && i2c_ifState.data_direction == DATA_DIRECTION_WRITE) {
            // the + 1 is because tokens[request_data_offset] = MESON_I2C_TOKEN_DATA but we want to store the token the come after
            if (wdata_offset < 4) {
                regs->wdata0 |= (data << (wdata_offset * 8));
            } else {
                regs->wdata1 |= (data << ((wdata_offset - 4) * 8));
            }
            // Since we grabbed the next token in the chain, increment offset
            wdata_offset++;
        }

        /* If data token and we are reading, increment counter of rdata */
        if ((meson_token == MESON_I2C_TOKEN_DATA || meson_token == MESON_I2C_TOKEN_DATA_END)
            && i2c_ifState.data_direction == DATA_DIRECTION_READ) {
            rdata_offset++;
        }

        request_data_offset++;
    }
    LOG_DRIVER("data loaded into registers!!\n");
    LOG_DRIVER("request_data_offset : 0x%lx, tk_offset: 0x%lx, wdata_offset: 0x%lx, rdata_offset: 0x%lx\n",
               request_data_offset, tk_offset, wdata_offset, rdata_offset);

    // Update remaining tokens indicator and start list processor
    i2c_ifState.remaining = i2c_ifState.curr_request_len - request_data_offset;

    LOG_DRIVER("Tokens loaded. %zu remain for this request\n", i2c_ifState.remaining);
    i2c_dump(regs);

    // Start list processor
    i2c_start(regs);
}

void init(void)
{
    i2c_setup();
    queue_handle = i2c_queue_init((i2c_queue_t *) request_region, (i2c_queue_t *) response_region);

    // Set up driver state
    i2c_ifState.curr_data = NULL;
    i2c_ifState.curr_request_len = 0;
    i2c_ifState.curr_response_len = 0;
    i2c_ifState.remaining = 0;
    i2c_ifState.notified = 0;
    i2c_ifState.addr = 0;

    microkit_dbg_puts("Driver initialised.\n");
}

static inline void handle_request(void)
{
    LOG_DRIVER("handling request\n");
    volatile struct i2c_regs *regs = (volatile struct i2c_regs *) i2c_regs;
    if (!i2c_queue_empty(queue_handle.request)) {
        // If this interface is busy, skip notification and
        // set notified flag for later processing
        if (i2c_ifState.curr_data) {
            LOG_DRIVER("driver: request in progress, deferring notification until later\n");
            i2c_ifState.notified = 1;
            return;
        }

        // Otherwise, begin work. Start by extracting the request
        size_t bus_address = 0;
        size_t offset = 0;
        unsigned int size = 0;
        int err = i2c_dequeue_request(queue_handle, &bus_address, &offset, &size);
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

        LOG_DRIVER("Loading request for bus address 0x%x of size %zu\n", bus_address, size);

        i2c_ifState.curr_data = (i2c_token_t *) DATA_REGIONS_START + offset;
        i2c_ifState.addr = bus_address;
        i2c_ifState.curr_request_len = size;
        i2c_ifState.remaining = size;
        i2c_ifState.notified = 0;

        i2c_load_tokens(regs);
    } else {
        LOG_DRIVER("called but no work available: resetting notified flag\n");
        // If nothing needs to be done, clear notified flag if it was set.
        i2c_ifState.notified = 0;
    }
}

/* Right now we do not do anything to handle a response timeout, even though we should
 * be. More investigation is required.
 * We observed very frequent timeout IRQs in our example system using an I2C card reader,
 * we believe the source of this problem is a misconfiguration with the clocks, and will
 * hopefully be resovled once we have an actual clock driver.
 * See https://github.com/au-ts/sddf/issues/212 for more details.
 */
static void handle_response_timeout(void)
{
    LOG_DRIVER("handling timeout IRQ\n");
    return;
}


static void handle_response(void)
{
    LOG_DRIVER("handling transfer complete IRQ\n");
    volatile struct i2c_regs *regs = (volatile struct i2c_regs *)i2c_regs;

    i2c_dump(regs);

    // Get result
    uint8_t curr_token = 0;
    uint8_t bytes_read = 0;
    bool write_error = i2c_get_error(regs, &bytes_read, &curr_token);

    // Prepare to extract data from the interface.
    // INVARIANT: request data is always smaller than returned data to allow
    //            reuse.
    i2c_token_t *return_buffer = i2c_ifState.curr_data;

    // If there was an error, cancel the rest of this transaction and load the
    // error information into the return buffer.
    if (write_error) {
        LOG_DRIVER("error!\n");
        // handle_response_timeout already has error logic for timeout
        if (curr_token == I2C_TOKEN_ADDR_READ) {
            return_buffer[RESPONSE_ERR] = I2C_ERR_NOREAD;
            LOG_DRIVER("I2C_ERR_NOREAD!\n");
        } else {
            return_buffer[RESPONSE_ERR] = I2C_ERR_NACK;
            LOG_DRIVER("I2C_ERR_NACK!\n");
        }
        // Token that caused the error
        return_buffer[RESPONSE_ERR_TOKEN] = curr_token;
        LOG_DRIVER("token that caused error: %d!\n", curr_token);

    } else {
        // Get bytes_read amount of read data

        // Copy data into return buffer
        for (int i = 0; i < bytes_read; i++) {
            size_t index = RESPONSE_DATA_OFFSET + i2c_ifState.curr_response_len;
            if (i < 4) {
                uint8_t value = (regs->rdata0 >> (i * 8)) & 0xFF;
                return_buffer[index] = value;
                LOG_DRIVER("loading into return_buffer at %d value 0x%lx\n", index, value);
            } else if (i < 8) {
                uint8_t value = (regs->rdata1 >> ((i - 4) * 8)) & 0xFF;
                return_buffer[index] = value;
                LOG_DRIVER("loading into return_buffer at %d value 0x%lx\n", index, value);
            }
            i2c_ifState.curr_response_len++;
        }

        LOG_DRIVER("I2C_ERR_OK\n");
        return_buffer[RESPONSE_ERR] = I2C_ERR_OK;
        // Token that caused error (could be anything since we set error code to no error anyway)
        return_buffer[RESPONSE_ERR_TOKEN] = 0x0;
    }

    // If request is completed or there was an error, return data to server and notify.
    if (write_error || !i2c_ifState.remaining) {
        LOG_DRIVER("request completed or error, hence returning response to server\n");
        LOG_DRIVER("curr_response_len : 0x%lx, curr_request_len : 0x%lx, return address is 0x%lx\n",
                   i2c_ifState.curr_response_len, i2c_ifState.curr_request_len, i2c_ifState.addr);
        LOG_DRIVER("enguing response with size: %d\n\n", i2c_ifState.curr_response_len + RESPONSE_DATA_OFFSET);
        // response length is + 2 (RESPONSE_DATA_OFFSET = 2) because of the error tokens at the start
        int ret = i2c_enqueue_response(queue_handle, i2c_ifState.addr,
                                       (size_t) i2c_ifState.curr_data - DATA_REGIONS_START,
                                       i2c_ifState.curr_response_len + RESPONSE_DATA_OFFSET);
        if (ret) {
            LOG_DRIVER_ERR("Failed to enqueue response\n");
        }

        // reset driver state for another request
        // load tokens resets the interface registers so no need here
        i2c_ifState.curr_response_len = 0;
        i2c_ifState.curr_data = NULL;
        i2c_ifState.curr_request_len = 0;
        i2c_ifState.remaining = 0;
        i2c_ifState.addr = 0;

        microkit_notify(VIRTUALISER_CH);

        i2c_halt(regs); // stop condition
    }

    // If the driver was notified while this transaction was in progress, immediately start working on the next one.
    // OR if there is still more work to do in current request, crack on with it.
    if (i2c_ifState.remaining) {
        LOG_DRIVER("Still work to do, starting next batch of tokens in request\n");
        i2c_load_tokens(regs); // results in a repeated start condition
    } else if (i2c_ifState.notified) {
        LOG_DRIVER("Was notified during transaction. Starting next client request immediately!\n");
        handle_request();
    }
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case VIRTUALISER_CH:
        handle_request();
        break;
    case IRQ_CH:
        handle_response();
        microkit_irq_ack(ch);
        break;
    case IRQ_TIMEOUT_CH:
        handle_response_timeout();
        microkit_irq_ack(ch);
        break;

    default:
        microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }
}
