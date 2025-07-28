//TODO: add licenses

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

struct spi_regs {
    uint32_t INTR_STATE;
    uint32_t INTR_ENABLE;
    uint32_t INTR_TEST;
    uint32_t ALERT_TEST; 
    uint32_t CONTROL;
    uint32_t STATUS;
    uint32_t CONFIGOPTS0;
    uint32_t CONFIGOPTS1;
    uint32_t CONFIGOPTS2;
    uint32_t CSID;
    uint32_t COMMAND;
    uint32_t RXDATA;
    uint32_t TXDATA;
    uint32_t ERROR_ENABLE;
    uint32_t ERROR_STATUS;
    uint32_t EVENT_ENABLE;
};

__attribute((__section__(".spi_driver_config"))) spi_driver_config_t config;
_Static_assert(sizeof(spi_driver_config_t) == 592);

__attribute((__section__(".device_resources"))) device_resources_t device_resources;

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
    }
    while (STATUS_ACTIVE(status) || STATUS_TXQD(status) != 0 || STATUS_RXQD(status) != 0);

    regs->CONTROL = 0;
}

/**
 * Brings the SPI host into a usable state
 */
static inline void device_setup(void)
{
    device_reset();

    // Enable the device
    regs->CONTROL = CONTROL_SPIEN | CONTROL_OUTPUT_EN;

    // The driver only cares when:
    // 1. TX FIFO is empty, and the driver should enqueue data
    // 2. RX FIFO is at the watermark, and the driver should dequeue data
    regs->EVENT_ENABLE = EVENT_ENABLE_TXEMPTY | EVENT_ENABLE_RXWM;

    // Set the receive watermark at the max
    regs->CONTROL |= CONTROL_RX_WATERMARK(FIFO_DEPTH * sizeof(uint32_t));

    // Recieve interrupts for all errors, since an unacknowledged error could halt the device
    regs->ERROR_ENABLE = ERROR_MASK; 

    // Enable only error interrupts, as enabling event interrupts would spam TXEMPTY
    regs->INTR_ENABLE = INTR_ERROR;

    // TODO: modify to fill in stuff statically
    // Setup all CS lines with default arguments
    regs->CONFIGOPTS0 = DEFAULT_DEVICE_CONFIG;
    regs->CONFIGOPTS1 = DEFAULT_DEVICE_CONFIG;
    regs->CONFIGOPTS2 = DEFAULT_DEVICE_CONFIG;

    // Poll status until the device is ready
    while (!STATUS_READY(regs->STATUS)) {} 
}

/**
 * Sets the watermark for the RX FIFO
 *
 * @param watermark the number of words in the RX FIFO which will trigger an interrupt
 */
static inline void set_rx_watermark(uint16_t watermark) {
    regs->CONTROL = 
        // Mask out RX_WATERMARK bits
        (regs->CONTROL & ~CONTROL_RX_WATERMARK_MASK) |
        // Set RX_WATERMARK
        CONTROL_RX_WATERMARK((uint32_t) watermark / sizeof(uint32_t));
}

/**
 * Poll the status register to see if the RX FIFO has entries
 * This is meant to guard against an incorrect driver or hardware
 *
 * @return 0 upon success, -1 upon timeout
 */
static inline int poll_rx(void) {
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
void transmit_data(const void *buffer, uint16_t len) {
    LOG_DRIVER("buffer=%p\n", buffer);
    const uint32_t *words = buffer;
    uint16_t num_words = len / sizeof(uint32_t);

    for (uint16_t i = 0; i < num_words; i++) {
        LOG_DRIVER("transmitting word %hu (%u)\n", i, words[i]);
        regs->TXDATA = words[i];
    }

    // Transmit trailing bytes
    const uint8_t *trailing_bytes = buffer + num_words * sizeof(uint32_t);
    uint16_t num_trailing_bytes = len % sizeof(uint32_t);

    for (uint16_t i = 0; i < num_trailing_bytes; i++) {
        LOG_DRIVER("transmitting trailing bytes\n");
        *((volatile uint8_t*) &regs->TXDATA) = trailing_bytes[i];
    }
}

/**
 * Recieves len bytes, and places them starting from buffer
 *
 * @param buffer the start of where to place the data
 * @param len the amount of bytes to recieve
 * @return 0 if successful, -1 if timed out while waiting for data
 */
int receive_data(void *buffer, uint16_t len) {
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
        LOG_DRIVER("returning early");
        return 0;
    }
    LOG_DRIVER("not returning early");
    
    if (poll_rx()) {
        return -1;
    }
    
    uint32_t remaining_data = regs->RXDATA;

    for (uint16_t i = 0; i < num_trailing_bytes; i++) {
        trailing_bytes[i] = ((uint8_t*) &remaining_data)[i];
    }
    
    return 0;
}
/**
 * IDLE: Resets the driver data, and processes the next transaction if available, sleeps otherwise
 * 
 * Succeeds: RESP
 *
 */
void state_idle(void) {
    spi_reset_state(&driver_data);

    spi_cs_queue_t *cs_queue = config.virt.cmd_cs_queue.vaddr;
    if (!spi_queue_empty(cs_queue->ctrl)) {
        fsm_state.nxt_state = SPI_STATE_CS;
    }
    else { 
        fsm_state.yield = true;
    }

    return;
}

void state_cs(void) {
    spi_cs_t cs;
    assert(!spi_dequeue_cs(config.virt.cmd_cs_queue.vaddr, &cs));
    driver_data.cs = cs;

    // Set which data region to operate in
    driver_data.data_region = config.data[cs].vaddr;

    // Set CS line
    regs->CSID = cs; 

    // Turn on SPI event interrupts, i.e. TX FIFO empty and RX FIFO at watermark
    regs->INTR_ENABLE |= INTR_SPI_EVENT;

    fsm_state.nxt_state = SPI_STATE_SEL_CMD;
}

void state_sel_cmd(void) {
    assert(!spi_dequeue_cmd(
        config.virt.cmd_queue.vaddr,
        &driver_data.read_offset,
        &driver_data.write_offset,
        &driver_data.len,
        &driver_data.cs_active_after_cmd
    ));
    LOG_DRIVER("read_offset=%lu, write_offset=%lu, len=%u, csaac=%u\n", driver_data.read_offset, driver_data.write_offset, driver_data.len, driver_data.cs_active_after_cmd);

    bool reading = driver_data.read_offset != -1;
    bool writing = driver_data.write_offset != -1;
    // Encoding 'not doing this op' as a fully completed op simplifies subsequent logic
    driver_data.tx_progress = writing ? 0 : driver_data.len;
    driver_data.rx_progress = reading ? 0 : driver_data.len;

    uint32_t spi_host_command = COMMAND_LEN_OFFSET(driver_data.len); 
    if (driver_data.cs_active_after_cmd) {
        spi_host_command |= COMMAND_CSAAT;
    }

    if (reading) {
        spi_host_command |= COMMAND_DIRECTION_RX_ONLY;
    }

    if (writing) {
        spi_host_command |= COMMAND_DIRECTION_TX_ONLY;
    }

    LOG_DRIVER("cmd=%x\n", spi_host_command);

    regs->COMMAND = spi_host_command; 

    fsm_state.nxt_state = SPI_STATE_CMD;
}

void state_cmd(void) {
    /*
     * Simultaneous reading and writing is special, as the FIFO access pattern 
     * (MISO and MOSI are still simultaneously active) looks like this:
     * 
     * TX: ***|***|***|... |*  |
     * RX:    |***|***|... |*  |***
     *
     * The |*  | fragment is due to being unable to specify differing amounts to read and write in
     * the same command
     *
     * This explains the ternary jumble below, where the len is determined by TX progress until the
     * very last FIFO access, which is RX-only
     * The jumble also handles read and write-only, since the first branch is selected when writing,
     * and the second branch is always selected when reading (see above where tx_progress is set)
     */
    uint16_t len = (driver_data.tx_progress < driver_data.len) ? 
        MIN(FIFO_DEPTH, driver_data.len - driver_data.tx_progress) :
        MIN(FIFO_DEPTH, driver_data.len - driver_data.rx_progress);
    LOG_DRIVER("len=%d\n", len);

    fsm_state.yield = true;

    // Implicitly encodes either a read-only, or write-read after the first write
    if (driver_data.rx_progress < driver_data.len && driver_data.tx_progress > 0) {
        void *rx_buffer = driver_data.data_region + driver_data.read_offset + 
            driver_data.rx_progress;
        if (receive_data(rx_buffer, len)) {
            //TODO: spi_setup(); since diff in amt of data cannot be reconciled easily
            driver_data.err = SPI_ERR_TIMEOUT;
            fsm_state.nxt_state = SPI_STATE_RESP;
            return;
        }
        driver_data.rx_progress += len;
        fsm_state.yield = fsm_state.yield && STATUS_RXQD(regs->STATUS) != len && 
            driver_data.rx_progress < driver_data.len; //TODO is this even sane?
    }

    // Set RX watermark if more words are expected
    if (driver_data.rx_progress < driver_data.len) {
        set_rx_watermark(len);
    }

    // Implicitly encodes either a write-only, or write-read before write completes
    if (driver_data.tx_progress < driver_data.len) {
        LOG_DRIVER(
            "data_region=%p, write_offset=%lu, tx_progress=%u\n",
            driver_data.data_region, driver_data.write_offset, driver_data.tx_progress
        );
        
        void *tx_buffer = driver_data.data_region + driver_data.write_offset + 
            driver_data.tx_progress;
        transmit_data(tx_buffer, len);
        driver_data.tx_progress += len;
        fsm_state.yield = fsm_state.yield && STATUS_TXQD(regs->STATUS) != 0;
    }

    fsm_state.nxt_state = SPI_STATE_CMD_RET;
}

void state_cmd_ret(void) { 
    // Implicitly encodes the completion conditions of all four cases: read-only, write-only, 
    // write-read, and dummy
    bool done = driver_data.tx_progress == driver_data.len && 
                driver_data.rx_progress == driver_data.len;

    if (!done && driver_data.read_offset != -1 && driver_data.write_offset != -1) {
        uint32_t status = regs->STATUS;
        if (!STATUS_TXEMPTY(status) || !STATUS_RXWM(status)) {
            LOG_DRIVER("Expecting another interrupt, sleeping\n");
            fsm_state.yield = true;
            return;
        }
    }

    fsm_state.nxt_state = 
        // Return to CMD if the command is uncompleted
        !done ? SPI_STATE_CMD :
        // Go to SEL_CMD if another command is expected
        driver_data.cs_active_after_cmd ? SPI_STATE_SEL_CMD :
            // Otherwise, respond to the finished transaction
            SPI_STATE_RESP;

    return;
}

void state_resp(void) {
    assert(!spi_enqueue_cs(config.virt.resp_cs_queue.vaddr, driver_data.cs));
    assert(!spi_enqueue_resp(config.virt.resp_queue.vaddr, driver_data.err, driver_data.cmd_in_progress));

    microkit_notify(config.virt.id);

    // Turn off SPI event interrupts, otherwise the driver will be spammed with TXEMPTY
    regs->INTR_ENABLE &= ~INTR_SPI_EVENT;

    fsm_state.nxt_state = SPI_STATE_IDLE;
}

void init(void) {
    assert(spi_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);   
 
    regs = (volatile struct spi_regs *)device_resources.regions[0].region.vaddr;
    LOG_DRIVER("regs=%p\n", regs);
    device_setup(); 

    for (uint8_t i = 0; i < SPI_CS_MAX; i++) {
        LOG_DRIVER("config[%2d] = {%p, %lu}\n", i, config.data[i].vaddr, config.data[i].size);
    }

    LOG_DRIVER("Driver initialised.\n");
}

void fsm(void) {
    do {
        spi_state_t state = fsm_state.nxt_state;
        LOG_DRIVER("Entering %s\n", fsm_str(state));
        switch (fsm_state.nxt_state) {
            case SPI_STATE_IDLE: {
                state_idle();
                break;
            }
            case SPI_STATE_CS: {
                state_cs();
                break;
            }
            case SPI_STATE_SEL_CMD: {
                state_sel_cmd();
                break;
            }
            case SPI_STATE_CMD: {
                state_cmd();
                break;
            }
            case SPI_STATE_CMD_RET: {
                state_cmd_ret();
                break;
            }
            case SPI_STATE_RESP: {
                state_resp();
                break;
            }
            default: {
                LOG_DRIVER_ERR("Entered erroneous state, defaulting back to IDLE\n");
                fsm_state.nxt_state = SPI_STATE_IDLE;
                fsm_state.yield = false;
            }
        }
        LOG_DRIVER("Exiting %s\n", fsm_str(state));
    } while (!fsm_state.yield);
    
    fsm_state.yield = false;
    return;
}

void handle_error(void) {
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
    }
    else {
        // Abort transaction if in progress
        switch (fsm_state.nxt_state) {
            case SPI_STATE_IDLE:
            case SPI_STATE_CS: {
                LOG_DRIVER_ERR("Going back to IDLE\n");
                fsm_state.nxt_state = SPI_STATE_IDLE;
                break;
            }
            case SPI_STATE_SEL_CMD:
            case SPI_STATE_CMD:
            case SPI_STATE_CMD_RET:
            case SPI_STATE_RESP: {
                LOG_DRIVER_ERR("Going to RESP\n");
                fsm_state.nxt_state = SPI_STATE_RESP;
                driver_data.err = SPI_ERR_OTHER;
                break;
            }
            default: {
                LOG_DRIVER_ERR("Handling error in invalid state, moving to IDLE\n");
                fsm_state.nxt_state = SPI_STATE_IDLE;
                break;
            }
        }
    }

    // Reset the device 
    device_setup();
}

void notified(microkit_channel ch) {
    LOG_DRIVER("Notified on channel %d\n", ch);

    // TODO: switch notification names
    if (ch == 0) { // error 
        LOG_DRIVER("status=%8X error=%8X\n", regs->STATUS, regs->ERROR_STATUS);
        handle_error();
        fsm();
        microkit_irq_ack(ch); 
    }
    else if (ch == 1) { // spi_event
        LOG_DRIVER("status=%8X error=%8X\n", regs->STATUS, regs->ERROR_STATUS);
        fsm();
        microkit_irq_ack(ch); 
    }
    else if (ch == config.virt.id) {
        fsm(); 
    }
    else {}
};

