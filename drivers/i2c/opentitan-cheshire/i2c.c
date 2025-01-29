/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// I2C controller (master) driver for the OpenTitan I2C IP block
// (https://opentitan.org/book/hw/ip/i2c/). Currently uses the memory map
// for the Cheshire SoC targeting the Digilent Genesys2, but this should
// be trivial to adapt for other boards/SoCs.
// https://pulp-platform.github.io/cheshire/tg/xilinx/
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 01/2025

#include <microkit.h>
#include <sddf/i2c/queue.h>
#include "cheshire-i2c.h"   // Alternate devices should replace this include and substitute
                            // another header at compile time, preferably via the makefile.
#include "driver.h"
#include "i2c.h"
#include <assert.h>

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("I2C DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif
#define LOG_DRIVER_ERR(...) do{ sddf_printf("I2C DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

/* Transport */
i2c_queue_handle_t queue_handle;
uintptr_t request_region;
uintptr_t response_region;

/* Internal state */
i2c_ifState_t driver_state;


/* Clock value calculations and timing*/
// NOTE: the `0 +` before each division is to fool the preprocessor into
// integer division.
#define MAX(a,b) ((0 + a) > (b) ? (a) : (b))
#define MIN(a,b) ((0 + a) < (b) ? (a) : (b))

i2c_timing_params_t timing_params = {
    .t_high_min = (MAX(((T_HIGH_MIN)/(T_CLK)), 4)),
    .t_low_min = (MAX(((T_HIGH_MIN)/(T_CLK)), 4)),
    .t_hd_dat_min = (MAX(((T_HD_DAT_MIN) / (T_CLK)), 1)),
    .t_hd_sta_min = (((T_HD_STA_MIN) / (T_CLK))),
    .t_su_sta_min = ((T_SU_STA_MIN) / (T_CLK)),
    .t_buf_min = ((T_BUF_MIN) / (T_CLK)),
    .t_sto_min = ((T_SU_STO_MIN) / (T_CLK)),
    .t_r = ((T_RISE) / (T_CLK)),
    .t_f = ((T_FALL) / (T_CLK))
};

/**
 * Write to a memory-mapped location. This is sized to match the registers of OpenTitan IPs.
 * This function should guarantee aligned, safe writes without memory reordering relative to
 * other memory region writes.
 */
static inline void i2c_mmio_write32(uintptr_t reg_offset, uint32_t value) {
    volatile uint32_t *base = (volatile uint32_t *)I2C_BASE_ADDR;
    base[reg_offset / sizeof(uint32_t)] = value;
}

/**
 * Read from a memory mapped location. This is the read-equivalent of i2c_mmio_write32.
 */
static inline uint32_t i2c_mmio_read32(uintptr_t reg_offset) {
    volatile uint32_t *base = (volatile uint32_t *)I2C_BASE_ADDR;
    return base[reg_offset / sizeof(uint32_t)];
}

static inline void load_timing_params(i2c_timing_params_t *p, uint32_t t_h, uint32_t t_l) {
    // TIMING0
    // 0:12 -> T_H, 16:28 -> T_L
    uint32_t timing0 = (t_h & I2C_TIMING0_THIGH_MASK)
        | ((t_l << I2C_TIMING0_TLOW_OFFSET) & I2C_TIMING0_TLOW_MASK);
    i2c_mmio_write32(I2C_TIMING0, timing0);

    // TIMING1
    // 0:9 -> T_R, 16:24 -> T_F
    uint32_t timing1 = (timing_params.t_r & I2C_TIMING1_T_R_MASK)
        | ((timing_params.t_f << I2C_TIMING1_T_F_OFFSET) & I2C_TIMING1_T_F_MASK);
    i2c_mmio_write32(I2C_TIMING1, timing1);

    // TIMING2
    // 0:12 -> TSU_STA, 16:28 -> THD_STA
    uint32_t timing2 = (timing_params.t_hd_sta_min & I2C_TIMING2_TSU_STA_MASK)
        | ((timing_params.t_su_sta_min << I2C_TIMING2_THD_STA_OFFSET) & I2C_TIMING2_THD_STA_MASK);
    i2c_mmio_write32(I2C_TIMING2, timing2);

    // TIMING3
    // 0:8 -> TSU_DAT, 16:28 -> THD_DAT
    uint32_t timing3 = (timing_params.t_su_dat_min & I2C_TIMING3_TSU_DAT_MASK)
        | ((timing_params.t_hd_dat_min << I2C_TIMING3_THD_DAT_OFFSET) & I2C_TIMING3_THD_DAT_MASK);
    i2c_mmio_write32(I2C_TIMING3, timing3);

    // TIMING4
    // 0:12 -> TSU_STO, 16:28 -> T_BUF
    uint32_t timing4 = (timing_params.t_sto_min & I2C_TIMING4_TSU_STO_MASK)
        | ((timing_params.t_buf_min << I2C_TIMING4_T_BUF_OFFSET) & I2C_TIMING4_T_BUF_MASK);
    i2c_mmio_write32(I2C_TIMING4, timing4);
}

void init(void)
{
    // Perform initial set up - calculate and validate timing parameters.
    // If any of the below conditions are not true, the device cannot initialise!
    assert(timing_params.t_hd_dat_min >= 1);
    assert(timing_params.t_hd_sta_min > timing_params.t_hd_dat_min);
    assert(timing_params.t_buf_min > timing_params.t_hd_dat_min);

    // Calculate periods - use device-supplied if faster than minimum.
    uint32_t period = MAX(((I2C_SCL_MIN_T) / (T_CLK)), ((SCL_PERIOD)/(T_CLK)));

    // T_H + T_L >= PERIOD - T_F - T_R
    // -> find T_H and T_L such that they fit and achieve duty cycle defined by board.
    // t_h = ( 100 * (T-T_F-T_R) ) / (duty_cycle*100)
    uint32_t t_h = ((100 * (period - T_FALL - T_RISE))/(DUTY_100X));

    // t_l = ( 100 * (T-T_F-T_R) ) / ((1 - duty_cycle)*100)
    uint32_t t_l = ((100 * (period - T_FALL - T_RISE))/(100 - DUTY_100X));

    // Check values are valid
    // Note: inequality appears backward here because the minimum period is actually the
    //       maximum speed. A lower period == a higher frequency. Hence, we check that
    //       f_h = (t_h^-1) < f_h_max since f = (t_h + t_l + t_f + t_r)^-1
    assert(t_h <= timing_params.t_high_min);
    assert(t_l <= timing_params.t_low_min);

    // Load timing parameters into registers
    load_timing_params(&timing_params, t_h, t_l);

    // Set up control register -> enable host mode, no other action for now.
    uint32_t ctrl = i2c_mmio_read32(I2C_CTRL);
    i2c_mmio_write32(I2C_CTRL, ctrl | (I2C_CTRL_ENHOST_MASK));

    // Prepare transport layer
    queue_handle = i2c_queue_init((i2c_queue_t *) request_region, (i2c_queue_t *) response_region);
    opentitan_i2c_reset_state(&driver_state);
    microkit_dbg_puts("Driver initialised.\n");
}

/**
 * Write a byte to the FMT FIFO.
 * @arg data: byte to write to FIFO
 * @arg flags: fmt_flags struct
*/
int i2c_fmt_write(uint8_t data, fdata_fmt_flags_t *flags) {
    // Parse flags
    // Validate using minterm function - if readb=X, rcont=Y, stop=W, nakok=Z, then
    // F = !X!Y + !W!Z + W!ZX!Y
    if(!((!flags->readb && !flags->rcont) || (!flags->stop && flags->nakok) ||
        (flags->stop && !flags->nakok && flags->readb && !flags->rcont))) {
        LOG_DRIVER_ERR("Invalid fmt flags supplied to i2c_write!");
        return -1;
    }
    uint32_t addr_fdata = (data) & I2C_FDATA_FBYTE_MASK;

    // Apply flags
    addr_fdata |= (flags->stop << I2C_FDATA_STOP_OFFSET) | (flags->rcont << I2C_FDATA_RCONT_OFFSET) |
        (flags->start << I2C_FDATA_START_OFFSET) | (flags->readb << I2C_FDATA_READB_OFFSET) |
        (flags->nakok << I2C_FDATA_NAKOK_OFFSET);

    i2c_mmio_write32(I2C_FDATA, addr_fdata);
    return 0;
}

static inline uint32_t get_fmt_fifo_lvl(void) {
    return i2c_mmio_read32(I2C_HOST_FIFO_STATUS) & I2C_HOST_FIFO_STATUS_FMTLVL_MASK;
}

/**
 * Given an sDDF I2C token, return an appropriately formatted OpenTitan fmt fifo entry.
 */
static inline uint32_t i2c_token_convert(i2c_token_t token) {
    switch (token) {
    case I2C_TOKEN_END:
        return ;
    case I2C_TOKEN_START:
        return ;
    case I2C_TOKEN_ADDR_WRITE:
        i2c_ifState.data_direction = DATA_DIRECTION_WRITE;
        return ;
    case I2C_TOKEN_ADDR_READ:
        i2c_ifState.data_direction = DATA_DIRECTION_READ;
        return ;
    case I2C_TOKEN_STOP:
        return ;
    default:
        LOG_DRIVER_ERR("invalid data token in request! \"0x%x\"\n", token);
        return -1;
    }

}

/**
 * Request contains invalid data or the hardware has failed, discard request.
 */
static void i2c_abort_request(void) {
    // TODO: return error to client
    opentitan_i2c_reset_state(&driver_state);
    return;
}

/**
 * Discover next I2C tokens and convert them into driver state. Extract upcoming flags, etc. to
 * create one interval consisting of a single read or write operation.
 */
static inline void new_interval(void) {
    // Translate incoming tokens. Since this IP is not token based we need to decode multiple
    // at a time. Whenever we detect a READ or WRITE, also read the next tokens to find all
    // START and STOP tokens before the next READ or WRITE.
    // NOTE: the END token has no direct effect for this hardware, it is ignored.
    i2c_token_t *tokens = driver_state.curr_data;
    i2c_token_t token = tokens[driver_state.req_idx];
    if (token != I2C_TOKEN_START && token != I2C_TOKEN_ADDR_WRITE
        && token != I2C_TOKEN_ADDR_READ) {
        LOG_DRIVER_ERR("Malformed request! Sequence must start with START, READ, or WRITE.");
        i2c_abort_request();
        return
    }

    // Handle each possible initial sequence and set format bits
    // Preamble: START or nothing
    // Body: READ or READC or WRITE
    // Tail: STOP

    // Check preamble
    if (token == I2C_TOKEN_START) {
        driver_state.int_has_start = true;
        driver_state.req_idx++;
        token = tokens[driver_state.req_idx];
    }

    // Check body
    if (token == I2C_TOKEN_ADDR_READC) {
        driver_state.data_direction = DATA_DIRECTION_READC;
    }
    else if (token == I2C_TOKEN_ADDR_READ) {
        driver_state.data_direction = DATA_DIRECTION_READ;
    } else if (token == I2C_TOKEN_ADDR_WRITE) {
        driver_state.data_direction = DATA_DIRECTION_WRITE;
    } else {
        // If any other data is here (likely an END), the token chain is broken and cannot be
        // represented in hardware.
        LOG_DRIVER_ERR("Spurious token in body of interval!");
        i2c_abort_request()
    }
    driver_state.interval_remaining =  tokens[driver_state.req_idx+1];
    driver_state.req_idx+= 2;
    token = tokens[driver_state.req_idx];

    // Check tail for reads. Writes need special handling as the stop token will only be after the
    // last payload byte, and this is detected in the load_tokens loop.
    if (driver_state.data_direction != DATA_DIRECTION_WRITE && token == I2C_TOKEN_STOP) {
        driver_state.int_has_stop = true;
        driver_state.req_idx++;
    }
}

static void i2c_load_tokens(void) {
    LOG_DRIVER("starting token load\n");
    LOG_DRIVER("Progress: %zu/%zu\n", driver_state.req_idx, driver_state.curr_request_len);

    i2c_token_t *tokens = driver_state.curr_data;

    // This IP block stores tokens of all types uniformly - as a single fmt fifo entry.
    // The fmt fifo is 64 entries long. We add data until the fmt_fifo is full and then
    // go to sleep.
    //
    // This driver breaks the incoming stream of tokens into intervals - an interval consists
    // of a single read/write token + any paired START/STOP tokens before or after it. The work in
    // an interval is divided into however many OpenTitan FMT fifo entries as needed.
    int batch_offset = 0;
    // TODO: add check for true FIFO fullness if needed.
    while (driver_state.curr_request_len - driver_state.req_idx > 0
        && batch_offset < OPENTITAN_I2C_FIFO_DEPTH) {
        fdata_fmt_flags_t flags = { 0, 0, 0, 0, 0 };
        uint8_t fmt_byte = 0;
        int remaining = driver_state.curr_request_len - driver_state.req_idx;

        // If the last interval is over, start a new one.
        if (driver_state.rw_remaining == 0) {
            new_interval();

            // Apply start if needed - can only trigger on first byte!
            if (driver_state.int_has_start) {
                flags.start = true;
            }
            continue;
        } else {
            // Otherwise, continue with current interval

            // Write case
            if (driver_state.data_direction & 1 == 0) {
                fmt_byte = driver_state[driver_state.req_idx];
                req_idx += 1;
                // Add stop flag on last byte of write
                if (remaining == 1 && driver_state.int_has_stop) {
                    flags.stop = true;
                }
            }
        }

        // Write to fmt
        i2c_fmt_write(fmt_byte, &flags);
    }

}

void handle_request(void) {
    if (!i2c_queue_empty(queue_handle.request)) {
        // Check if work is in progress. Only allow one transaction at a time in FIFOs.
        if (driver_state.req_idx != 0) {
            LOG_DRIVER("driver: request in progress, deferring notification until later\n");
            driver_state.notified = 1;
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
        if (bus_address > I2C_MAX_BUS_ADDRESS) {
            LOG_DRIVER_ERR("attempted to write to address > 7-bit range!\n");
            return;
        }

        LOG_DRIVER("Loading request for bus address 0x%x of size %zu\n", bus_address, size);

        driver_state.curr_data = (i2c_token_t *) DATA_REGIONS_START + offset;
        driver_state.addr = bus_address;
        driver_state.curr_request_len = size;
        driver_state.req_idx = 0;
        driver_state.notified = 0;

        i2c_load_tokens();
    } else {
        LOG_DRIVER("Called but queue is empty, resetting.");
        i2c_ifstate.notified = 0;
    }
}

void handle_response(void) {

}

void notified(microkit_channel ch)
{
    switch (ch) {
    case VIRTUALISER_CH:
        handle_request();
        break;
    case IRQ
        handle_response();
        microkit_irq_ack(ch);
        break;

    case IRQ_RXTHRESH_CH:
    case IRQ_FMTTHRESH_CH:
    case IRQ_RXOVERFLOW_CH:
    default:
        microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }
}
