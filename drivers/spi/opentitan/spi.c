/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/spi/config.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include "driver.h"

#define DEBUG_DRIVER
#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("SPI DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("SPI DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

__attribute((__section__(".spi_driver_config"))) spi_driver_config_t config;

__attribute((__section__(".device_resources"))) device_resources_t device_resources;

spi_handle_t virt_handle;

// MMIO registers
volatile struct spi_regs *regs;

// FSM state
fsm_state_t fsm_state;
spi_driver_data_t driver_data;

/**
 * Resets the SPI host
 */
static inline void device_reset(void)
{
    // Reset SPI host
    regs->CONTROL = CONTROL_SW_RST;

    // Poll status until inactive and both FIFOs are drained
    uint32_t status;
    do {
        status = regs->STATUS;
    } while (STATUS_ACTIVE(status) || STATUS_TXQD(status) != 0 || STATUS_RXQD(status) != 0);

    regs->CONTROL = 0;
}

/**
 *
 */
static inline uint32_t pack_config(spi_device_config_t *config)
{
    uint32_t temp = CONFIGOPTS_CLKDIV(config->freq_div);
    if (config->cpha) {
        temp |= CONFIGOPTS_CPHA;
    }
    if (config->cpol) {
        temp |= CONFIGOPTS_CPOL;
    }
    return temp;
}

/**
 * Brings the SPI host into a usable state
 */
static inline void device_setup(void)
{
    device_reset();

    // Enable the device
    regs->CONTROL = CONTROL_SPIEN | CONTROL_OUTPUT_EN;

    // Interrupt when IDLE
    regs->EVENT_ENABLE = EVENT_ENABLE_IDLE | EVENT_ENABLE_RXFULL | EVENT_ENABLE_TXEMPTY | EVENT_ENABLE_RXWM;

    // Set the receive watermark at the max
    regs->CONTROL |= CONTROL_RX_WATERMARK(FIFO_DEPTH / sizeof(uint32_t) - 1);

    // Recieve interrupts for all errors, since an unacknowledged error could halt the device
    regs->ERROR_ENABLE = ERROR_MASK;

    // Enable only error interrupts, as enabling event interrupts would spam TXEMPTY
    regs->INTR_ENABLE = INTR_ERROR;

    // Setup all CS lines with default arguments
    regs->CONFIGOPTS0 = pack_config(&config.dev_config[0]);
    regs->CONFIGOPTS1 = pack_config(&config.dev_config[1]);
    regs->CONFIGOPTS2 = pack_config(&config.dev_config[2]);

    // Poll status until the device is ready
    while (!STATUS_READY(regs->STATUS)) {}
}

/**
 * Poll the status register to see if the RX FIFO has entries
 * This is meant to guard against an incorrect driver or hardware
 *
 * @return 0 upon success, -1 upon timeout
 */
static inline int poll_rx(void)
{
    for (uint16_t timeout = 0; timeout < TIMEOUT_LIMIT; timeout++) {
        if (STATUS_RXQD(regs->STATUS)) {
            return 0;
        }
    }

    LOG_DRIVER_ERR("Polling RX timed out\n");
    return -1;
}

/**
 * Transmits len bytes starting from buffer
 *
 * @param buffer the start of the data
 * @param len the len of the data in bytes
 */
void transmit_data(const void *buffer, uint16_t len)
{
    const uint32_t *words = buffer;
    uint16_t num_words = len / sizeof(uint32_t);

    for (uint16_t i = 0; i < num_words; i++) {
        LOG_DRIVER("Transmitting: %08X\n", words[i]);
        regs->TXDATA = words[i];
    }

    // Transmit trailing bytes
    const uint8_t *trailing_bytes = buffer + num_words * sizeof(uint32_t);
    uint16_t num_trailing_bytes = len % sizeof(uint32_t);

    for (uint16_t i = 0; i < num_trailing_bytes; i++) {
        LOG_DRIVER("Transmitting: %02X\n", trailing_bytes[i]);
        *((volatile uint8_t *)&regs->TXDATA) = trailing_bytes[i];
    }
}

/**
 * Recieves len bytes, and places them starting from buffer
 *
 * @param buffer the start of where to place the data
 * @param len the amount of bytes to recieve
 * @return 0 if successful, -1 if timed out while waiting for data
 */
int receive_data(void *buffer, uint16_t len)
{
    uint32_t *words = buffer;
    uint16_t num_words = len / sizeof(uint32_t);

    for (uint16_t i = 0; i < num_words; i++) {
        if (poll_rx()) {
            return -1;
        }

        words[i] = regs->RXDATA;
    }

    // Retrieve trailing bytes
    uint8_t *trailing_bytes = buffer + num_words * sizeof(uint32_t);
    uint16_t num_trailing_bytes = len % sizeof(uint32_t);

    if (num_trailing_bytes == 0) {
        LOG_DRIVER("returning early\n");
        return 0;
    }
    LOG_DRIVER("not returning early\n");

    if (poll_rx()) {
        return -1;
    }

    uint32_t remaining_data = regs->RXDATA;

    for (uint16_t i = 0; i < num_trailing_bytes; i++) {
        trailing_bytes[i] = ((uint8_t *)&remaining_data)[i];
    }

    return 0;
}

/**
 * IDLE: Resets the driver data, and processes the next transaction if available, sleeps otherwise
 *
 * Succeeds: RESP
 *
 */
void state_idle(void)
{
    spi_reset_state(&driver_data);

    if (!spi_cmd_cs_queue_empty(&virt_handle)) {
        // Turn on SPI event interrupts, i.e. the device is idling
        regs->INTR_ENABLE |= INTR_SPI_EVENT;

        fsm_state.nxt_state = SPI_STATE_GET_CS;
    } else {
        fsm_state.yield = true;
    }
}

void state_get_cs(void)
{
    assert(spi_dequeue_cmd_cs(&virt_handle, &driver_data.cs));
    driver_data.data_region = config.data[driver_data.cs].vaddr;

    LOG_DRIVER("cs=%u\n", driver_data.cs);

    // Set CS line
    regs->CSID = driver_data.cs;

    fsm_state.nxt_state = SPI_STATE_GET_LOGICAL_CMD;
}

void state_get_logical_cmd(void)
{
    uint16_t cmd_len;
    assert(spi_dequeue_cmd(&virt_handle, &driver_data.read_offset, &driver_data.write_offset, &cmd_len,
                           &driver_data.cs_active_after_cmd));
    driver_data.len = CMD_LEN(cmd_len);
    driver_data.logical_progress = 0;

    LOG_DRIVER("read_offset=%lu, write_offset=%lu, len=%u, csaac=%u\n", driver_data.read_offset,
               driver_data.write_offset, driver_data.len, driver_data.cs_active_after_cmd);

    fsm_state.nxt_state = SPI_STATE_ISSUE_PHY_CMD;
}

void state_issue_phy_cmd(void)
{
    driver_data.phy_cmd_len = MIN(driver_data.len - driver_data.logical_progress, COMMAND_LEN_MAX);
    if (driver_data.phy_cmd_len == 0) {
        if (driver_data.cs_active_after_cmd) {
            driver_data.cmd_in_progress++;
            fsm_state.nxt_state = SPI_STATE_GET_LOGICAL_CMD;
        } else {
            driver_data.err = SPI_STATUS_OK;
            fsm_state.nxt_state = SPI_STATE_RESP;
        }
        return;
    }

    driver_data.tx_progress = 0;
    driver_data.rx_progress = 0;

    uint32_t command = COMMAND_LEN(driver_data.phy_cmd_len);
    if (driver_data.read_offset != -1) {
        command |= COMMAND_DIRECTION_RX_ONLY;
    }
    if (driver_data.write_offset != -1) {
        command |= COMMAND_DIRECTION_TX_ONLY;
    }
    bool final_phy_cmd = driver_data.logical_progress + driver_data.phy_cmd_len == driver_data.len;
    if (driver_data.cs_active_after_cmd || !final_phy_cmd) {
        command |= COMMAND_CSAAT;
    }

    LOG_DRIVER("COMMAND=%x\n", command);

    regs->COMMAND = command;

    fsm_state.nxt_state = SPI_STATE_EXEC_PHY_CMD;
}

void state_exec_phy_cmd(void)
{
    /**
     * When simultaneously reading and writing, the FIFO access pattern looks something like this:
     *
     * TX: ***|***| ... |***|*
     * RX:    |***| ... |***|***|*
     *
     * Some of the oddities in the logic (i.e. ternary for determining rx_len, the rw_first and
     * rw_last variable, etc.) are to enable the access pattern
     */
    bool reading = driver_data.read_offset != -1;
    bool writing = driver_data.write_offset != -1;

    const void *tx_buffer = driver_data.data_region + driver_data.write_offset + driver_data.logical_progress
                          + driver_data.tx_progress;
    void *rx_buffer = driver_data.data_region + driver_data.read_offset + driver_data.logical_progress
                    + driver_data.rx_progress;
    uint16_t tx_len = MIN(FIFO_DEPTH, driver_data.phy_cmd_len - driver_data.tx_progress);
    uint16_t rx_len = (!writing) ? MIN(FIFO_DEPTH, driver_data.phy_cmd_len - driver_data.rx_progress)
                                 : driver_data.tx_progress - driver_data.rx_progress;

    bool rw_first = driver_data.tx_progress == 0;
    bool rw_last = !rw_first && driver_data.rx_progress + rx_len == driver_data.phy_cmd_len;

    if (writing && !(reading && rw_last)) {
        transmit_data(tx_buffer, tx_len);
        driver_data.tx_progress += tx_len;
    }

    if (reading && !(writing && rw_first)) {
        if (receive_data(rx_buffer, rx_len)) {
            // Re-setup the device to recover
            device_setup();
            driver_data.err = SPI_STATUS_ERR_TIMEOUT;
            fsm_state.nxt_state = SPI_STATE_RESP;
            return;
        }
        driver_data.rx_progress += rx_len;
    }

    fsm_state.yield = true;
    fsm_state.nxt_state = SPI_STATE_AWAIT_PHY_CMD;
}

void state_await_phy_cmd(void)
{
    bool reading = driver_data.read_offset != -1;
    bool writing = driver_data.write_offset != -1;
    bool read_done = driver_data.rx_progress == driver_data.phy_cmd_len;
    bool write_done = driver_data.tx_progress == driver_data.phy_cmd_len;

    bool done;
    if (reading && writing) {
        done = read_done && write_done;
#ifdef DEBUG_DRIVER
        uint32_t status = regs->STATUS;
        assert(STATUS_TXQD(status) == 0);
        assert(done || STATUS_RXQD(status) > 0);
#endif /* DEBUG_DRIVER */
    } else if (reading) {
        done = read_done;
#ifdef DEBUG_DRIVER
        assert(done || STATUS_RXQD(regs->STATUS) > 0);
#endif /* DEBUG_DRIVER */
    } else if (writing) {
        done = write_done;
#ifdef DEBUG_DRIVER
        assert(STATUS_TXQD(regs->STATUS) == 0);
#endif /* DEBUG_DRIVER */
    } else {
        done = true;
#ifdef DEBUG_DRIVER
        assert(!STATUS_ACTIVE(regs->STATUS));
#endif /* DEBUG_DRIVER */
    }

    if (done) {
        driver_data.logical_progress += driver_data.phy_cmd_len;
        fsm_state.nxt_state = SPI_STATE_ISSUE_PHY_CMD;
    } else {
        fsm_state.nxt_state = SPI_STATE_EXEC_PHY_CMD;
    }

    return;
}

void state_resp(void)
{
    assert(spi_enqueue_resp_cs(&virt_handle, driver_data.cs));
    assert(spi_enqueue_resp(&virt_handle, driver_data.err, driver_data.cmd_in_progress));

    microkit_notify(config.virt.id);

    // Turn off SPI event interrupts, otherwise the driver will be spammed with TXEMPTY
    regs->INTR_ENABLE &= ~INTR_SPI_EVENT;

    fsm_state.nxt_state = SPI_STATE_IDLE;
}

void fsm(void)
{
    do {
        spi_state_t state = fsm_state.nxt_state;
        LOG_DRIVER("Entering %s\n", fsm_str(state));
        switch (fsm_state.nxt_state) {
        case SPI_STATE_IDLE:
            state_idle();
            break;
        case SPI_STATE_GET_CS:
            state_get_cs();
            break;
        case SPI_STATE_GET_LOGICAL_CMD:
            state_get_logical_cmd();
            break;
        case SPI_STATE_ISSUE_PHY_CMD:
            state_issue_phy_cmd();
            break;
        case SPI_STATE_EXEC_PHY_CMD:
            state_exec_phy_cmd();
            break;
        case SPI_STATE_AWAIT_PHY_CMD:
            state_await_phy_cmd();
            break;
        case SPI_STATE_RESP:
            state_resp();
            break;
        default:
            LOG_DRIVER_ERR("Entered erroneous state, defaulting back to IDLE\n");
            fsm_state.nxt_state = SPI_STATE_IDLE;
            fsm_state.yield = false;
        }
        LOG_DRIVER("Exiting %s\n", fsm_str(state));
    } while (!fsm_state.yield);

    fsm_state.yield = false;
    return;
}

void handle_error(void)
{
    uint32_t error = regs->ERROR_STATUS;

    // Log all errors
    if (error & ERROR_ACCESSINVAL) {
        LOG_DRIVER_ERR("Zero byte write\n");
    }
    if (error & ERROR_CSIDINVAL) {
        LOG_DRIVER_ERR("CSID was set incorrectly: 0x%08X\n", regs->CSID);
    }
    if (error & ERROR_CMDINVAL) {
        LOG_DRIVER_ERR("Invalid command\n");
    }
    if (error & ERROR_UNDERFLOW) {
        LOG_DRIVER_ERR("Attempted to read RX FIFO when empty\n");
    }
    if (error & ERROR_OVERFLOW) {
        LOG_DRIVER_ERR("Attempted to write to TX FIFO when full\n");
    }
    if (error & ERROR_CMDBUSY) {
        LOG_DRIVER_ERR("Wrote command while not ready\n");
    }

    if (!(error & ERROR_MASK)) {
        LOG_DRIVER_ERR("Recieved error IRQ but no errors\n");
    } else {
        // Abort transaction if in progress
        switch (fsm_state.nxt_state) {
        case SPI_STATE_IDLE:
        case SPI_STATE_GET_CS:
            LOG_DRIVER_ERR("Going back to IDLE\n");
            fsm_state.nxt_state = SPI_STATE_IDLE;
            break;
        case SPI_STATE_GET_LOGICAL_CMD:
        case SPI_STATE_ISSUE_PHY_CMD:
        case SPI_STATE_EXEC_PHY_CMD:
        case SPI_STATE_AWAIT_PHY_CMD:
        case SPI_STATE_RESP:
            LOG_DRIVER_ERR("Going to RESP\n");
            fsm_state.nxt_state = SPI_STATE_RESP;
            driver_data.err = SPI_STATUS_ERR_OTHER;
            break;
        default:
            LOG_DRIVER_ERR("Handling error in invalid state, moving to IDLE\n");
            fsm_state.nxt_state = SPI_STATE_IDLE;
            break;
        }
    }

    // Reset the device
    device_setup();
}

void init(void)
{
    // Check configuration is correct
    assert(spi_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.irqs[0].id == ERROR_IRQ);
    assert(device_resources.irqs[1].id == EVENT_IRQ);
    assert(device_resources.num_regions == 1);

    // Check handle initialization is correct
    assert(spi_handle_init(&virt_handle, config.virt.cmd_queue.vaddr, config.virt.resp_queue.vaddr,
                           config.virt.cmd_cs_queue.vaddr, config.virt.resp_cs_queue.vaddr,
                           config.virt.queue_capacity_bits));

    regs = (volatile struct spi_regs *)device_resources.regions[0].region.vaddr;
    device_setup();

    LOG_DRIVER("Driver initialised.\n");
}

void notified(microkit_channel ch)
{
    LOG_DRIVER("Notified on channel %d\n", ch);

    if (ch == ERROR_IRQ) {
        LOG_DRIVER("Error IRQ recieved: ");
        LOG_DRIVER("STATUS=%08X, ERROR=%08X\n", regs->STATUS, regs->ERROR_STATUS);
        handle_error();
        fsm();
        microkit_irq_ack(ch);
    } else if (ch == EVENT_IRQ) {
        LOG_DRIVER("Event IRQ recieved: ");
        LOG_DRIVER("STATUS=%08X, ERROR=%08X\n", regs->STATUS, regs->ERROR_STATUS);
        fsm();
        microkit_irq_ack(ch);
    } else if (ch == config.virt.id) {
        fsm();
    } else {
        LOG_DRIVER("Supriously notified on channel %u\n", ch);
    }
};
