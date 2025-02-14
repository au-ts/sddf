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
#include <sddf/i2c/config.h>
#include <sddf/resources/device.h>
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

/* sdfgen */
__attribute__((__section__(".i2c_driver_config"))) i2c_driver_config_t config;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

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
    .t_hd_sta_min = (((0 + T_HD_STA_MIN) / (T_CLK))),
    .t_su_sta_min = ((0 + T_SU_STA_MIN) / (T_CLK)),
    .t_buf_min = ((0 + T_BUF_MIN) / (T_CLK)),
    .t_sto_min = ((0 + T_SU_STO_MIN) / (T_CLK)),
    .t_r = ((0 + T_RISE) / (T_CLK)),
    .t_f = ((0 + T_FALL) / (T_CLK)),
    .t_h = 0,
    .t_l = 0
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

static inline void load_timing_params(i2c_timing_params_t *p) {
    // TIMING0
    // 0:12 -> T_H, 16:28 -> T_L
    uint32_t timing0 = (timing_params.t_h & I2C_TIMING0_THIGH_MASK)
        | ((timing_params.t_l << I2C_TIMING0_TLOW_OFFSET) & I2C_TIMING0_TLOW_MASK);
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
    // Check sdfgen properties
    assert(i2c_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 4);
    assert(device_resources.num_regions == 1);

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
    timing_params.t_h = ((100 * (period - T_FALL - T_RISE))/(DUTY_100X));

    // t_l = ( 100 * (T-T_F-T_R) ) / ((1 - duty_cycle)*100)
    timing_params.t_l = ((100 * (period - T_FALL - T_RISE))/(100 - DUTY_100X));

    // Check values are valid
    // Note: inequality appears backward here because the minimum period is actually the
    //       maximum speed. A lower period == a higher frequency. Hence, we check that
    //       f_h = (t_h^-1) < f_h_max since f = (t_h + t_l + t_f + t_r)^-1
    assert(timing_params.t_h <= timing_params.t_high_min);
    assert(timing_params.t_l <= timing_params.t_low_min);

    // Load timing parameters into registers
    load_timing_params(&timing_params);

    // Set up control register -> enable host mode, no other action for now.
    uint32_t ctrl = i2c_mmio_read32(I2C_CTRL);
    i2c_mmio_write32(I2C_CTRL, ctrl | (I2C_CTRL_ENHOST_MASK));

    // Set up interrupts
    uint32_t intr_enable = i2c_mmio_read32(I2C_INTR_ENABLE);
    intr_enable |= I2C_INTR_ENABLE_FMT_THRESHOLD_BIT;
    intr_enable |= I2C_INTR_ENABLE_RX_THRESHOLD_BIT;
    intr_enable |= I2C_INTR_ENABLE_CONTROLLER_HALT_BIT;
    intr_enable |= I2C_INTR_ENABLE_CMD_COMPLETE_BIT;
    i2c_mmio_write32(I2C_INTR_ENABLE, intr_enable);

    // Configure host FIFO
    uint32_t host_fifo_config = i2c_mmio_read32(I2C_HOST_FIFO_CONFIG);
    host_fifo_config |= (I2C_FMT_THRESHOLD) & I2C_HOST_FIFO_CONFIG_FMTTHRESH_MASK;
    host_fifo_config |= (I2C_RX_THRESHOLD << I2C_HOST_FIFO_CONFIG_RXTHRESH_OFFSET)
                        & I2C_HOST_FIFO_CONFIG_RXTHRESH_MASK;
    i2c_mmio_write32(I2C_HOST_FIFO_CONFIG, host_fifo_config);

    // Prepare transport layer
    queue_handle = i2c_queue_init(config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr);
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
    bool flags_valid = ((!flags->readb && !flags->rcont) || (!flags->stop && flags->nakok) ||
        (flags->stop && !flags->nakok && flags->readb && !flags->rcont));
    if(!flags_valid) {
        LOG_DRIVER_ERR("Invalid fmt flags supplied to i2c_write! Combination cannot be represented "
                        "by hardware!");
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
 * If the CONTROLLER_HALT interrupt is asserted, find the error cause.
 */
static inline i2c_err_t i2c_get_error(void) {
    uint32_t host_events = i2c_mmio_read32(I2C_CONTROLLER_EVENTS);
    if (!host_events) {
        return I2C_ERR_OK;
    }
    // Return first detected event in order of importance (same as bit order).
    if (host_events & I2C_CONTROLLER_EVENTS_NACK_BIT) {
        LOG_DRIVER_ERR("Transaction failed! Device sent unexpected NACK.");
        return I2C_ERR_NACK;
    }
    if (host_events & I2C_CONTROLLER_EVENTS_UNHANDLED_NACK_TIMEOUT_BIT) {
        LOG_DRIVER_ERR("Transaction failed! NACK timeout threshold reached.");
        return I2C_ERR_TIMEOUT;
    }
    if (host_events & I2C_CONTROLLER_EVENTS_BUS_TIMEOUT_BIT) {
        LOG_DRIVER_ERR("Transaction failed! Bus timeout.");
        return I2C_ERR_TIMEOUT;
    }
    if (host_events & I2C_CONTROLLER_EVENTS_ARBITRATION_LOST_BIT) {
        LOG_DRIVER_ERR("Transaction failed! Lost arbitration to another host!");
    }
    return I2C_ERR_OTHER;
}

/**
 * If something has gone wrong, return the request and terminate transaction.
 */
void handle_error_response(i2c_error_t err) {
    LOG_DRIVER_ERR("Returning with error...");
    i2c_token_t *return_buffer = driver_state.curr_data;
    return_buffer[RESPONSE_ERR_TOKEN] = driver_state.curr_data[driver_state.req_idx];
    return_buffer[RESPONSE_ERR] = err;

    // Return
    int ret = i2c_enqueue_response(queue_handle, driver_state.addr,
                                  (size_t)driver_state.curr_data - (uintptr_t)config.virt.data.vaddr,
                                  driver_state.curr_response_len + RESPONSE_DATA_OFFSET);
    if (ret) {
        LOG_DRIVER_ERR("Failed to enqueue response!\n");
    }
    opentitan_i2c_reset_state(&driver_state);
    microkit_notify(config.virt.id);
}
/**
 * Request contains invalid data or the hardware has failed, discard request.
 */
static void i2c_abort_request(void) {
    opentitan_i2c_reset_state(&driver_state);
    handle_error_response(i2c_get_error());
    return;
}

/**
 * Discover next I2C tokens and convert them into driver state. Extract upcoming flags, etc. to
 * create one interval consisting of a single read or write operation. If nothing is left to do,
 * reset.
 */
static inline void new_interval(void) {
    // Translate incoming tokens. Since this IP is not token based we need to decode multiple
    // at a time. Whenever we detect a READ or WRITE, also read the next tokens to find all
    // START and STOP tokens before the next READ or WRITE.
    if (driver_state.req_idx >= driver_state.int_read_remaining) {
        // Nothing to do.
        LOG_DRIVER("new_interval triggered with no work to do!");
        return;
    }

    i2c_token_t *tokens = driver_state.curr_data;
    i2c_token_t token = tokens[driver_state.req_idx];
    if (token != I2C_TOKEN_START && token != I2C_TOKEN_ADDR_WRITE
        && token != I2C_TOKEN_ADDR_READ) {
        LOG_DRIVER_ERR("Malformed request! Interval must start with START, READ, or WRITE.");
        i2c_abort_request();
        return;
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
    assert(driver_state.interval_remaining == 0);
    driver_state.interval_remaining =  tokens[driver_state.req_idx+1];
    if (token == I2C_TOKEN_ADDR_READC) {
        driver_state.data_direction = DATA_DIRECTION_READC;
    } else if (token == I2C_TOKEN_ADDR_READ) {
        driver_state.data_direction = DATA_DIRECTION_READ;
        // Skip padding bytes after read.
        driver_state.req_idx += tokens[driver_state.req_idx+1];
    } else if (token == I2C_TOKEN_ADDR_WRITE) {
        driver_state.data_direction = DATA_DIRECTION_WRITE;
    } else {
        // If any other data is here (likely an END), the token chain is broken and cannot be
        // represented in hardware.
        LOG_DRIVER_ERR("Spurious token in body of interval!");
        i2c_abort_request();
        return;
    }
    // Skip body token and length
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
    while (driver_state.curr_request_len - driver_state.req_idx > 0) {
        // Check there is room in fmt. If we're full, stop working and wait until the FIFO
        // sends the threshold IRQ to indicate it has space again.
        if (get_fmt_fifo_lvl() == OPENTITAN_I2C_FIFO_DEPTH) { // Convert to use status reg instead?
            LOG_DRIVER("FMT FIFO is full! Deferring operation...");
            driver_state.token_load_await_fmt = true;
            if (driver_state.request_await_fmt) {
                // NOTE: the code can actually handle the below case, it just should never occur
                //       as it implies that data is potentially mixing between requests which
                //       shouldn't happen for any reason with the protocol design.
                LOG_DRIVER_ERR("CRITICAL: a request in progress and a pending request are both "
                               "awaiting the FMT FIFO to empty. This should never happen!");
            }
            return;
        }
        fdata_fmt_flags_t flags = { 0, 0, 0, 0, 0 };
        uint8_t fmt_byte = 0;
        int remaining = driver_state.int_read_remaining - driver_state.req_idx;

        // If the last interval is over, start a new one.
        if (driver_state.interval_remaining == 0) {
            new_interval();

            // Apply start if needed - can only trigger on first byte!
            if (driver_state.int_has_start) {
                flags.start = true;
            }
        }
        // Write case - we only can find the length and token ahead of time.
        if (driver_state.data_direction & 1 == 0) {
            fmt_byte = driver_state[driver_state.req_idx];
            driver_state.req_idx++;
            // Add stop flag on last byte of write if there is a trailing STOP token
            if (remaining == 1 && tokens[driver_state.req_idx] == I2C_TOKEN_STOP) {
                flags.stop = true;
                driver_state.req_idx++; // Skip stop token
            }
        } else {
            // Read case
            // Request up to OPENTITAN_I2C_READ_MAX at a time
            fmt_byte = driver_state.interval_remaining % OPENTITAN_I2C_READ_MAX;
            driver_state.interval_remaining -= fmt_byte;    // Subtract read count

            // Trigger `rcont` if this is:
            // a. not the last batch of a READ
            // b. this is a READC
            if (driver_state.interval_remaining ||
                driver_state.data_direction == DATA_DIRECTION_READC) {
                flags.rcont = true;
            }

            // Trigger `stop` if this is the final write and the flag is required.
            if (!driver_state.interval_remaining && driver_state.int_has_stop) {
                flags.stop = true;
            }
            // Reads don't take more tokens as they work!
        }

        // Write to fmt
        i2c_fmt_write(fmt_byte, &flags);
    }
}

static inline bool fmt_fifo_empty(void) {
    return (i2c_mmio_read32(I2C_STATUS) & I2C_STATUS_FMTEMPTY_BIT) != 0);
}

/**
 * Returns True if the driver has an active request.
 */
static inline bool request_in_progress(void) {
    return ((uint8_t)driver_state.curr_data == 0);
}

void handle_request(void) {
    if (!i2c_queue_empty(queue_handle.request)) {
        // Check if work is in progress. Only allow one transaction at a time in FIFOs.
        if (request_in_progress()) {
            LOG_DRIVER("Request in progress, deferring notification until later\n");
            driver_state.notified = 1;
            return;
        }

        // Check that FIFO is ready for a new transaction. We only permit a new request once the
        // FMT fifo is completely empty.
        if (!fmt_fifo_empty) {
            LOG_DRIVER("New request started but FMT FIFO isn't empty yet. Deferring.");
            driver_state.request_await_fmt = true;
            return;
        }

        // Otherwise, begin work. Start by resetting and extracting the request
        opentitan_i2c_reset_state(driver_state);
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

        driver_state.curr_data = (i2c_token_t *)config.virt.data.vaddr + offset;
        driver_state.addr = bus_address;
        driver_state.int_read_remaining = size;
        driver_state.req_idx = 0;
        driver_state.notified = 0;

        i2c_load_tokens();
    } else {
        LOG_DRIVER("Called but queue is empty, resetting.");
        i2c_ifstate.notified = 0;
    }
}

static inline bool rx_fifo_not_empty() {
    uint32_t status = i2c_mmio_read32(I2C_STATUS);
    return(status & I2C_STATUS_RXEMPTY_BIT == 0);
}

/**
 * Handle data in the RX FIFO. Accept whatever bytes are present and put in return buffer.
 */
void handle_rdata(void) {
    if (!rx_fifo_not_empty()) {
        LOG_DRIVER_ERR("WARNING: handle_response called but RX FIFO is empty!");
        return;
    }
    // Prepare to extract data from the interface.
    // INVARIANT: request data is always smaller than returned data to allow
    //            reuse.
    i2c_token_t *return_buffer = i2c_ifState.curr_data;

    // Extract data from RDATA. This needs to happen with minimal overhead because this function
    // will be triggered whenever any amount of data is available in the read data FIFO.
    // In future, this can be optimised by dynamically adjusting the read FIFO irq threshold
    // to only trigger as frequently as needed for a given read operation.
    while (rx_fifo_not_empty() && driver_state.resp_idx < driver_state.int_read_len) {
        size_t idx = RESPONSE_DATA_OFFSET + driver_state.curr_response_len;
        uint8_t data = ((uint8_t)i2c_mmio_read32(RDATA)) & 0xFF;
        return_buffer[idx] = data;
        driver_state.interval_remaining--;
    }
    if (rx_fifo_not_empty()) {
        LOG_DRIVER_ERR("WARNING: RX fifo contains more data than current read interval!");
    }
    // We only know how many bytes we've read back out of the currently requested bytes. We should
    // stop immediately as soon as we have read the number we expect.
    // TODO: handle case where spurious data appears. Should just drop as this should never happen?
    //       We can't leave data behind either as any spurious byte is not guaranteed to be read
    //       again unless a "respond again" flag or similar is set
}

/**
 * Clear bits causing controller halt in CONTROLLER_EVENTS. Causes I2C to resume functioning.
 */
static inline void i2c_reset_controller() {
    i2c_mmio_write32(I2C_CONTROLLER_EVENTS, (uint32_t)0);
}



/**
 * Handle returning data in a successful case.
 */
void handle_response() {
    LOG_DRIVER("Returning data to virt");
    i2c_token_t *return_buffer = i2c_ifState.curr_data;
    return_buffer[RESPONSE_ERR_TOKEN] = 0;
    return_buffer[RESPONSE_ERR] = I2C_ERR_OK;
    int ret = i2c_enqueue_response(queue_handle, driver_state.addr,
                                  (size_t)driver_state.curr_data - (uintptr_t)config.virt.data.vaddr,
                                  driver_state.curr_response_len + RESPONSE_DATA_OFFSET);
    if (ret) {
        LOG_DRIVER_ERR("Failed to enqueue response!\n");
    }
    opentitan_i2c_reset_state(&driver_state);
    microkit_notify(config.virt.id);
}

void notified(microkit_channel ch)
{
    /*
     * This device has several possible ending conditions:
     * a. If no reads are outstanding / last op was a write, and all fmt data sent,
     *    CMD_COMPLETE irq is asserted. If the FMT FIFO is also empty, we are done.
     * b. If a read was outstanding, the read IRQ might be processed AFTER CMD_COMPLETE.
     *    In this event, we wait to return the data until interval_remaining == 0 (i.e. all bytes
     *    returned). Once we have accounted for all data and the FMT fifo is empty, we are done.
     *    This means we must have the possibility to terminate on IRQ_RX_THRESH.
     * c. Something has gone wrong. CONTROLLER_HALT irq is asserted and we give up.
     *
     * The docs imply that a token leaving the FMT FIFO guarantees a result has also appeared.
     * i.e. the moment the FMT_FIFO threshold IRQ fires to indicate emptiness, a read token will
     * have also resolved if the last op was a read.
     */
    bool fmt_empty = i2c_mmio_read32(uintptr_t reg_offset)
    bool driver_done = driver_state.req_idx == driver_state.curr_request_len;
    switch (ch) {
    case VIRTUALISER_CH:
        handle_request();
        break;
    case IRQ_FMTTHRESH_CH:
        // Asserted when FMT FIFO has < 1 entry.
        LOG_DRIVER("IRQ_FMTTHRESH");

        // Continue loading tokens if an in-progress request was halted due to FIFO fullness.
        if (driver_state.token_load_await_fmt) {
            driver_state.token_load_await_fmt = false;
            i2c_load_tokens();
            LOG_DRIVER("Deferred token load serviced.");
        } else if (driver_state.request_await_fmt) {
            // If a request was deferred due to the FMT fifo having data, resume.
            driver_state.request_await_fmt = false;
            handle_request();
            LOG_DRIVER("Deferred request serviced.");
        }
        microkit_irq_ack(ch);
        break;
    case IRQ_RXTHRESH_CH:
        // Asserted when RX FIFO has < 1 entry.
        handle_rdata();
        // Handle case of the last byte(s) of a read landing after CMD_COMPLETE.
        if (driver_done && driver_state.interval_remaining == 0) {
            handle_response();
        }
        microkit_irq_ack(ch);
        break;
    case IRQ_CMD_COMPLETE:
        // If there are no reads outstanding AND we are done, finish up.
        if (driver_done && driver_state.interval_remaining == 0) {
            handle_response();
        } else if (driver_done) {
            LOG_DRIVER("CMD_COMPLETE with driver done but interval is outstanding! Deferring.");
        }
        microkit_irq_ack(ch);
        break;
    case IRQ_CONTROLLER_HALT:
        // Transaction has failed!
        i2c_abort_request();
        i2c_reset_controller();
        microkit_irq_ack(ch);
        break;
    default:
        microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }

    // If there is no pending request, check if we deferred a new one.
    if (!request_in_progress && driver_state.notified) {
        LOG_DRIVER("Starting deferred request...");
        driver_state.notified = 0;
        handle_request();
    }
}
