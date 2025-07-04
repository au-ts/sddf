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

__attribute((__section__(".device_resources"))) device_resources_t device_resources;

// MMIO registers
volatile struct spi_regs *regs;

// Request and response queues
spi_queue_handle_t queue_handle;

// FSM state
fsm_state_t fsm_state;
spi_driver_data_t driver_data;

/**
 * Resets the SPI host
 */
static inline void spi_reset(void)
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
static inline void spi_setup(void)
{
    spi_reset();

    // Enable the device
    regs->CONTROL = CONTROL_SPIEN | CONTROL_OUTPUT_EN;

    // Control which SPI events interrupt
    regs->EVENT_ENABLE = EVENT_ENABLE_TXEMPTY | EVENT_ENABLE_RXWM;

    // Set the recieve watermark at the max
    regs->CONTROL |= CONTROL_RX_WATERMARK(RX_FIFO_WORD_DEPTH);

    // Control which errors interrupt
    regs->ERROR_ENABLE = ERROR_MASK; 

    // Enable only error interrupts
    regs->INTR_ENABLE = INTR_ERROR;

    // Setup all CS lines with default arguments
    regs->CONFIGOPTS0 = DEFAULT_DEVICE_CONFIG;
    regs->CONFIGOPTS1 = DEFAULT_DEVICE_CONFIG;
    regs->CONFIGOPTS2 = DEFAULT_DEVICE_CONFIG;

    // Poll status until the device is ready
    while (!STATUS_READY(regs->STATUS)) {} 
}

void set_rx_watermark(uint16_t watermark) {
    regs->CONTROL = 
        // Mask non-RX_WATERMARK bits
        (regs->CONTROL & ~CONTROL_RX_WATERMARK_MASK) | 
        // Set RX_WATERMARK
        CONTROL_RX_WATERMARK((uint32_t) watermark / sizeof(uint32_t));
}

// ret 0 if successful, -1 otherwise not
int poll_rx(void) {
    for (uint16_t timeout = 0; timeout < TIMEOUT_LIMIT; timeout++) {
        if (STATUS_RXQD(regs->STATUS)) {
            return 0;
        }
    }

    LOG_DRIVER_ERR("Polling RX timed out\n");
    return -1;
}

void transmit_data(void *buffer, uint16_t len) {
    volatile uint8_t *TX_BYTE = (uint8_t *) &regs->TXDATA;

    // Transmit leading bytes to word align buffer
    uint8_t *leading_bytes = buffer;
    uint16_t bytes_until_aligned = ALIGN(buffer, sizeof(uint32_t)) - buffer;
    uint16_t num_leading_bytes = MIN(len, bytes_until_aligned); 

    for (uint16_t i = 0; i < num_leading_bytes; i++) {
        *TX_BYTE = leading_bytes[i];
    }

    bool done = num_leading_bytes != bytes_until_aligned;
    if (done) {
        return;
    }

    // Transmit as many words as possible
    uint32_t *words = buffer + num_leading_bytes;
    uint16_t num_words = (len - num_leading_bytes) / sizeof(uint32_t);

    for (uint16_t i = 0; i < num_words; i++) {
        regs->TXDATA = words[i];
    }

    // Transmit trailing bytes
    uint8_t *trailing_bytes = buffer + num_leading_bytes + num_words * sizeof(uint32_t);
    uint16_t num_trailing_bytes = (len - num_leading_bytes) % sizeof(uint32_t);

    for (uint16_t i = 0; i < num_trailing_bytes; i++) {
        *TX_BYTE = trailing_bytes[i];
    }
}

int recieve_data(void *buffer, uint16_t len) {
    // Recieve leading bytes to word align buffer
    uint8_t *leading_bytes = buffer;
    const uint16_t bytes_until_aligned = ALIGN(buffer, sizeof(uint32_t)) - buffer;
    const uint16_t num_leading_bytes = MIN(len, bytes_until_aligned); 

    // Treat rx_data as queue
    uint64_t rx_data = 0;
    uint8_t *rx_byte = (uint8_t *) &rx_data;

    if (num_leading_bytes > 0) {
        if (poll_rx()) {
            return -1;
        }
        rx_data = regs->RXDATA;

        for (uint16_t i = 0; i < num_leading_bytes; i++) {
            leading_bytes[i] = rx_byte[i];
        } 
        rx_data >>= num_leading_bytes * 8;

        bool done = num_leading_bytes != bytes_until_aligned;
        if (done) {
            return 0;
        }
    }

    // Transmit as many words as possible
    uint32_t *words = buffer + num_leading_bytes;
    const uint16_t num_words = (len - num_leading_bytes) / sizeof(uint32_t);

    for (uint16_t i = 0; i < num_words; i++) {
        if (poll_rx()) {
            return -1;
        }

        rx_data |= regs->RXDATA << (sizeof(uint32_t) - num_leading_bytes) * 8; 
        words[i] = rx_data;
        rx_data >>= sizeof(uint32_t) * 8;
    }

    // Transmit trailing bytes
    uint8_t *trailing_bytes = buffer + num_leading_bytes + num_words * sizeof(uint32_t);
    const uint16_t num_trailing_bytes = (len - num_leading_bytes) % sizeof(uint32_t);

    if (num_trailing_bytes == 0) {
        return 0;
    }
    
    if (poll_rx()) {
        return -1;
    }
    rx_data |= regs->RXDATA << (sizeof(uint32_t) - num_leading_bytes) * 8;
    for (uint16_t i = 0; i < num_trailing_bytes; i++) {
        trailing_bytes[i] = rx_byte[i];
    }
    
    return 0;
}

void state_idle(void) {
    spi_reset_state(&driver_data);

    if (!spi_queue_empty(queue_handle.request->ctrl)) {
        fsm_state.nxt_state = REQ;
    }
    else { 
        fsm_state.yield = true;
    }

    return;
}

void state_req(void) {
    int err = spi_dequeue_request(
        queue_handle,
        &driver_data.cs_line,
        (uintptr_t *) &driver_data.cmd,
        (uintptr_t *) &driver_data.slice_base, 
        &driver_data.num_cmds
    );

    if (err) {
        LOG_DRIVER_ERR("fatal: failed to dequeue request\n"); 
        // Do not respond, as a failed dequeue implies there is no request 
        // to respond to
        fsm_state.nxt_state = IDLE;
        return;
    }

    // Check if the amount of commands make sense
    if (driver_data.num_cmds > SPI_CMD_CAPACITY) {
        LOG_DRIVER_ERR("amount of supplied commands exceeds the capacity");
        driver_data.err = SPI_ERR_OTHER; //TODO: change
        fsm_state.nxt_state = RESP;
        return;
    }

    // Set the CS line
    if (driver_data.cs_line > PULP_MAX_CS_LINE) {
        driver_data.err = SPI_ERR_INVALID_CS_LINE;
        fsm_state.nxt_state = RESP;
        return;
    } 
    regs->CSID = driver_data.cs_line; 

    // Turn on SPI event interrupts
    regs->INTR_ENABLE |= INTR_SPI_EVENT;

    driver_data.cmd_in_progress = 0;

    fsm_state.nxt_state = SEL_CMD;
}

void state_sel_cmd(void) {
    // Go to RESP once all commands have been completed
    if (driver_data.cmd_in_progress >= driver_data.num_cmds) {
        driver_data.cmd_in_progress = -1;
        driver_data.err = SPI_ERR_OK;
        fsm_state.nxt_state = RESP;
        return;
    }

    // Sleep, wait for device to become ready 
    if (!STATUS_READY(regs->STATUS)) {
        fsm_state.yield = true;
        return;
    }

    spi_cmd_t *cmd = &driver_data.cmd[driver_data.cmd_in_progress];

    // Check if the command is valid
    if (cmd->mode >= NUM_MODES) {
        driver_data.err = SPI_ERR_INVALID_CMD;
        fsm_state.nxt_state = RESP;
        return;
    }

    // Do bounds checking
    config.slice_size = 0x1000; //TODO: gotta update sdfgen :(
    bool read_oob = cmd->read_offset  + cmd->len >= config.slice_size;
    bool write_oob = cmd->write_offset + cmd->len >= config.slice_size;
    LOG_DRIVER("read offset=%zu, write offset=%zu, len=%hu, slice_sz=%zu\n",
        cmd->read_offset, cmd->write_offset, cmd->len, config.slice_size);

    switch(cmd->mode) {
        case SPI_READ: {
            if (read_oob) {
                driver_data.err = SPI_ERR_OOB;
                fsm_state.nxt_state = RESP;
                return;
            }
            break;
        }
        case SPI_WRITE: {
            if (write_oob) {
                driver_data.err = SPI_ERR_OOB;
                fsm_state.nxt_state = RESP;
                return;
            }
            break;
        }
        case SPI_TRANSFER: {
            if (read_oob || write_oob) {
                driver_data.err = SPI_ERR_OOB;
                fsm_state.nxt_state = RESP;
                return;
            }

            if (
                /* Slices do not completely overlap */
                cmd->read_offset != cmd->write_offset &&
                /* Slices are not disjoint */
                (cmd->read_offset >= cmd->write_offset + cmd->len ||
                cmd->write_offset >= cmd->read_offset + cmd->len)
            ) {
                driver_data.err = SPI_ERR_OTHER; //TODO: change error
                fsm_state.nxt_state = RESP; 
            }

            break;
        }
        default: {}
    }

    driver_data.tx_remaining = cmd->len;
    driver_data.rx_remaining = cmd->len;
    fsm_state.nxt_state = CMD;
}

void state_cmd(void) {
    spi_cmd_t *cmd = &driver_data.cmd[driver_data.cmd_in_progress];
    uint32_t hw_cmd_len = 0;
    uint32_t spi_host_command;
    bool tx_complete = driver_data.tx_remaining == 0;
    bool final_command = false;

    switch (cmd->mode) {
    case SPI_READ:
        hw_cmd_len = MIN(driver_data.rx_remaining, RX_FIFO_BYTE_DEPTH); 
        final_command = driver_data.rx_remaining - hw_cmd_len == 0;
        spi_host_command = COMMAND_DIRECTION_RX_ONLY;
        // Set RX watermark to interrupt when it has recieved all data
        set_rx_watermark(hw_cmd_len);
        break;
    case SPI_WRITE:
        hw_cmd_len = MIN(driver_data.tx_remaining, TX_FIFO_BYTE_DEPTH);
        final_command = driver_data.tx_remaining - hw_cmd_len == 0;
        spi_host_command = COMMAND_DIRECTION_TX_ONLY;
        break;
    /**
     * SPI_TRANSFER is special, as the FIFO access pattern* looks like this:
     * 
     * TX: ***|***|***|... |*  |
     * RX:    |***|***|... |*  |***
     *
     * The |*  | fragment is due to being unable to specify differing
     * amounts to read and write in the same command, which results in the 
     * ternary jumble below
     * *MISO and MOSI are still simultaneously active
     */
    case SPI_TRANSFER:
        hw_cmd_len = 
            (tx_complete) ?
                MIN(driver_data.rx_remaining, MIN_FIFO_BYTE_DEPTH) :
                MIN(driver_data.tx_remaining, MIN_FIFO_BYTE_DEPTH);
        final_command = driver_data.rx_remaining - hw_cmd_len == 0;
        spi_host_command = COMMAND_DIRECTION_BIDIRECTION;
        // Set RX watermark to interrupt when it has recieved all data
        set_rx_watermark(hw_cmd_len);
        break;
    default:
        driver_data.err = SPI_ERR_INVALID_CMD;
        fsm_state.nxt_state = RESP;
        return;
    }

    spi_host_command |= COMMAND_LEN_OFFSET(hw_cmd_len); 
    // TODO: add meaningful comment
    if (!(driver_data.cmd_in_progress == driver_data.num_cmds - 1 && final_command)) {
        spi_host_command |= COMMAND_CSAAT;
    }
    sddf_printf("cmd=%x\n", spi_host_command);
    
    /* TODO: perhaps move everything beyond into SEL_CMD? */

    regs->COMMAND = spi_host_command; 

    void *write_buffer = (void *)
        // Pointer to base of the command's data to write
        driver_data.slice_base + cmd->write_offset +
        // Can alternatively expressed as TX progress
        cmd->len - driver_data.tx_remaining;
    void *read_buffer = (void *)
        // Pointer to base of the command's data to read
        driver_data.slice_base + cmd->read_offset + 
        // Can alternatively expressed as RX progress
        cmd->len - driver_data.rx_remaining;

    switch (cmd->mode) {
    case SPI_READ:
        if (recieve_data(read_buffer, hw_cmd_len)) {
            driver_data.err = SPI_ERR_OTHER; //TODO: replace
            fsm_state.nxt_state = RESP;
            return;
        }
        driver_data.rx_remaining -= hw_cmd_len;
        fsm_state.yield = STATUS_RXQD(regs->STATUS) != hw_cmd_len;
        break;
    case SPI_WRITE:
        transmit_data(write_buffer, hw_cmd_len);
        driver_data.tx_remaining -= hw_cmd_len;
        fsm_state.yield = STATUS_TXQD(regs->STATUS) != 0;
        break;
    case SPI_TRANSFER:
        // As noted above, this is meant to reflect the FIFO access pattern
        if (!tx_complete) {
            transmit_data(write_buffer, hw_cmd_len);
            driver_data.tx_remaining -= hw_cmd_len;
        }

        bool first = driver_data.tx_remaining == hw_cmd_len;
        if (!first) {
            if (recieve_data(read_buffer, hw_cmd_len)) {
                driver_data.err = SPI_ERR_OTHER; //TODO: replace
                fsm_state.nxt_state = RESP;
                return;
            }
            driver_data.rx_remaining -= hw_cmd_len;
        }

        // Yield only if the command has not fully executed already
        uint32_t status = regs->STATUS;
        fsm_state.yield = (STATUS_RXQD(status) != hw_cmd_len) || 
                          (STATUS_TXQD(status) != 0);

        break;
    default:
        driver_data.err = SPI_ERR_INVALID_CMD;
        fsm_state.nxt_state = RESP;
        break;
    }

    fsm_state.nxt_state = CMD_RET;
}

void state_cmd_ret(void) { 
    spi_cmd_t *cmd = &driver_data.cmd[driver_data.cmd_in_progress];

    bool done = false;
    bool write_done = driver_data.tx_remaining == 0;
    bool read_done = driver_data.rx_remaining == 0;

    switch (cmd->mode) {
        case SPI_READ: {
            done = read_done;
            break;
        }
        case SPI_WRITE: {
            done = write_done;
            break;
        }
        case SPI_TRANSFER: {
            done = write_done && read_done;

            uint32_t status = regs->STATUS;
            if (!done && !(STATUS_TXEMPTY(status) && STATUS_RXWM(status))) {
                LOG_DRIVER("Expecting another interrupt, sleeping\n");
                fsm_state.yield = true;
                return;
            }
            break;
        }
        default: {
            driver_data.err = SPI_ERR_INVALID_CMD;
            fsm_state.nxt_state = RESP;
            return;
        }
    }

    if (done) {
        driver_data.cmd_in_progress++;
        fsm_state.nxt_state = SEL_CMD;
    }
    else {
        // Continue with current command if unfinished
        fsm_state.nxt_state = CMD;
    }

    return;
}

void state_resp(void) {
    int err = spi_enqueue_response(
        queue_handle, 
        driver_data.cs_line,  
        driver_data.err,
        driver_data.cmd_in_progress
    );

    if (err) {
        LOG_DRIVER_ERR("Cannot enqueue response\n");
        return;
    }

    microkit_deferred_notify(config.virt.id);

    // Turn off SPI event interrupts, otherwise the driver will be spammed with
    // TXEMPTY
    regs->INTR_ENABLE &= ~INTR_SPI_EVENT;    

    fsm_state.nxt_state = IDLE; 
}

void init(void) {
    assert(spi_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);   
 
    regs = (volatile struct spi_regs *)device_resources.regions[0].region.vaddr;
    spi_setup(); 

    queue_handle = spi_queue_init(
        config.virt.req_queue.vaddr, 
        config.virt.resp_queue.vaddr
    );

    microkit_dbg_puts("Driver initialised.\n");
}

void fsm(void) {
    do {
        spi_state_t state = fsm_state.nxt_state;
        LOG_DRIVER("Entering %s\n", fsm_str(state));
        switch (fsm_state.nxt_state) {
            case IDLE: {
                state_idle();
                break;
            }
            case REQ: {
                state_req();
                break;
            }
            case SEL_CMD: {
                state_sel_cmd();
                break;
            }
            case CMD: {
                state_cmd();
                break;
            }
            case CMD_RET: {
                state_cmd_ret();
                break;
            }
            case RESP: {
                state_resp();
                break;
            }
            default: {
                LOG_DRIVER_ERR("Entered erroneous state, defaulting back to IDLE\n");
                fsm_state.nxt_state = IDLE;
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
            case IDLE:
            case REQ: {
                LOG_DRIVER_ERR("Going back to IDLE\n");
                fsm_state.nxt_state = IDLE;
                break;
            }
            case SEL_CMD:
            case CMD:
            case CMD_RET:
            case RESP: {
                LOG_DRIVER_ERR("Going to RESP\n");
                fsm_state.nxt_state = RESP;
                driver_data.err = SPI_ERR_OTHER;
                break;
            }
            default: {
                LOG_DRIVER_ERR("Handling error in invalid state, moving to IDLE\n");
                fsm_state.nxt_state = IDLE;
                break;
            }
        }
    }

    // Reset the device 
    spi_setup();
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

seL4_MessageInfo_t protected(microkit_channel ch, seL4_MessageInfo_t msginfo) {
    size_t label = microkit_msginfo_get_label(msginfo);
    if (label != SPI_BUS_CONFIG) {
        LOG_DRIVER_ERR("unknown label 0x%zx given by virt\n", label);
        return microkit_msginfo_new(SPI_FAILURE, 0);
    }

    size_t argc = microkit_msginfo_get_count(msginfo);
    if (argc != SPI_BUS_CONFIG_ARGC) {
        LOG_DRIVER_ERR("expected %d arguments, virt sent %zu instead\n", 
            SPI_BUS_CONFIG_ARGC, argc);
        return microkit_msginfo_new(SPI_FAILURE, 0);
    }

    volatile uint32_t *config_reg = NULL;
    uint32_t config = 0;

    size_t bus = microkit_mr_get(SPI_BUS_SLOT);
    switch (bus) {
    case 0: 
        config_reg = &regs->CONFIGOPTS0;
        break;
    case 1:
        config_reg = &regs->CONFIGOPTS1;
        break;
    case 2:
        config_reg = &regs->CONFIGOPTS2;
        break;
    default:
        LOG_DRIVER_ERR("virt gave invalid bus 0x%zx\n", bus);
        return microkit_msginfo_new(SPI_FAILURE, 0);
    } 

    size_t cpol = microkit_mr_get(SPI_CPOL_SLOT);
    switch (cpol) {
    case SPI_CPOL_LOW:
        break;
    case SPI_CPOL_HIGH:
        config |= CONFIGOPTS_CPOL;
        break;
    default:
        LOG_DRIVER_ERR("virt gave invalid clock polarity 0x%zx on bus 0x%zx\n",
            cpol, bus);
        return microkit_msginfo_new(SPI_FAILURE, 0);
    }

    size_t cpha = microkit_mr_get(SPI_CPHA_SLOT);
    switch (cpha) {
    case SPI_CPHA_FIRST:
        break;
    case SPI_CPHA_SECOND:
        config |= CONFIGOPTS_CPHA;
        break;
    default:
        LOG_DRIVER_ERR("virt gave invalid clock phase 0x%zx on bus 0x%zx\n",
            cpha, bus);
    }

    *config_reg |= config;

    return microkit_msginfo_new(SPI_SUCCESS, 0);
}

