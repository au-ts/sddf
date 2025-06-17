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

//TODO: define failure condition
/**
 * Resets the SPI host
 */
static inline void spi_reset(void)
{
    // Reset SPI host
    regs->CONTROL = CONTROL_SW_RST;

    // Poll status until inactive and both FIFOs are drained
    for (int i = 0; i < TIMEOUT_LIMIT; i++) {
        uint32_t status = regs->STATUS; 
        if (!STATUS_ACTIVE(status) && STATUS_TXQD(status) == 0 && 
            STATUS_RXQD(status) == 0) {
            regs->CONTROL = 0;
            return;
        }
    }
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
    regs->CONTROL |= CONTROL_RX_WATERMARK(RX_FIFO_DEPTH);

    // Control which errors interrupt
    regs->ERROR_ENABLE = 
        ERROR_CSIDINVAL |
        ERROR_CMDINVAL |
        ERROR_UNDERFLOW |
        ERROR_OVERFLOW |
        ERROR_CMDBUSY;

    // Enable interrupts
    regs->INTR_ENABLE = INTR_ERROR;

    // Poll status until the device is ready
    while (!STATUS_READY(regs->STATUS)) {} 
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
    uint16_t bytes_until_aligned = 
        ALIGN(buffer, sizeof(uint32_t)) - buffer;
    uint16_t num_leading_bytes = MIN(len, bytes_until_aligned); 

    for (uint16_t i = 0; i < num_leading_bytes; i++) {
        *TX_BYTE = leading_bytes[i];
    }

    bool done = num_leading_bytes != bytes_until_aligned;
    if (done)
        return;

    // Transmit as many words as possible
    uint32_t *words = buffer + num_leading_bytes;
    uint16_t num_words = (len - num_leading_bytes) / sizeof(uint32_t);

    for (uint16_t i = 0; i < num_words; i++) {
        regs->TXDATA = words[i];
    }

    // Transmit trailing bytes
    uint8_t *trailing_bytes = 
        buffer + num_leading_bytes + num_words * sizeof(uint32_t);
    uint16_t num_trailing_bytes = (len - num_leading_bytes) % sizeof(uint32_t);

    for (uint16_t i = 0; i < num_trailing_bytes; i++) {
        *TX_BYTE = trailing_bytes[i];
    }
}

// Precondition:
// 1. buffer is word-aligned or
// 2. len < 4
void recieve_data(void *buffer, uint16_t len) {
    // Recieve as many words as possible 
    uint32_t *words = buffer;
    uint16_t num_words = len / sizeof(uint32_t);

    for (uint16_t i = 0; i < num_words; i++) {
        sddf_printf("iteration %d of %d\n", i, num_words);   
        if (poll_rx()) {
            return;
        }
        words[i] = regs->RXDATA;
    }
 
    // Recieve trailing bytes
    uint16_t num_trailing_bytes = len % sizeof(uint32_t);
    if (num_trailing_bytes > 0) {
        sddf_printf("trailing\n");

        if (poll_rx()) {
            return;
        }

        // Effectively convert the unsigned int into a byte array
        // Assumes the processor is big-endian
        uint32_t remaining_bytes = regs->RXDATA;
        uint8_t *trailing_bytes = (uint8_t *) &remaining_bytes;
        uint8_t *buffer_byte = buffer + num_words * sizeof(uint32_t);

        for (uint16_t i = 0; i < num_trailing_bytes; i++) {
            buffer_byte[i] = trailing_bytes[i];
        }
    }
}

void state_idle(void) {
    spi_reset_state(&driver_data);

    if (!spi_queue_empty(queue_handle.request->ctrl)) {
        // Turn on SPI event interrupts
        regs->INTR_ENABLE |= INTR_SPI_EVENT;
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
        (uintptr_t *) &driver_data.buffer_base, 
        &driver_data.num_cmds
    );

    if (err) {
        LOG_DRIVER_ERR("fatal: failed to dequeue request\n"); 
        // Do not respond, as a failed dequeue implies there is no request 
        // to respond to
        fsm_state.nxt_state = IDLE;
        return;
    }

    if (driver_data.cs_line > PULP_MAX_CS_LINE) {
        driver_data.err = SPI_ERR_INVALID_CS_LINE;
        fsm_state.nxt_state = RESP;
        return;
    } 

    regs->CSID = driver_data.cs_line; 
    driver_data.cmd_in_progress = 0;

    fsm_state.nxt_state = SEL_CMD;
}

void state_sel_cmd(void) {
    if (driver_data.cmd_in_progress >= driver_data.num_cmds) {
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

    // Do bounds checking on each command
    config.buffer_size = 0x1000; //TODO: gotta update sdfgen :(
    bool read_oob = cmd->read_offset  + cmd->len >= config.buffer_size;
    bool write_oob = cmd->write_offset + cmd->len >= config.buffer_size;
    LOG_DRIVER("read offset=%zu, write offset=%zu, len=%hu, buffer_sz=%zu\n",
        cmd->read_offset, cmd->write_offset, cmd->len, config.buffer_size);

    // TODO: probably need to clean this up
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
            break;
        }
        default: {}
    }

    driver_data.tx_progress = 0;
    driver_data.rx_progress = 0;
    fsm_state.nxt_state = CMD;
}

void state_cmd(void) {
    spi_cmd_t *cmd = &driver_data.cmd[driver_data.cmd_in_progress];
    uint32_t cmd_len = 0;
    /**
     * This command only toggles SCLK, doesn't transmit from the TXFIFO or
     * recieve any data into RXFIFO
     */
    uint32_t spi_host_command = COMMAND_LEN_OFFSET(1); 
    bool tx_complete = driver_data.tx_progress == cmd->len;

    switch (cmd->mode) {
        case SPI_READ: {
            cmd_len = MIN(cmd->len - driver_data.rx_progress, RX_FIFO_DEPTH); 
            spi_host_command = COMMAND_DIRECTION_RX_ONLY;
            // Set RX watermark to interrupt at
            regs->CONTROL = (regs->CONTROL & ~CONTROL_RX_WATERMARK_MASK) | CONTROL_RX_WATERMARK(cmd->len);
            break;
        }
        case SPI_WRITE: {
            cmd_len = MIN(cmd->len - driver_data.tx_progress, TX_FIFO_DEPTH);
            spi_host_command = COMMAND_DIRECTION_TX_ONLY;
            break;
        }
        /**
         * SPI_TRANSFER is special, as the FIFO access pattern (NOT THE
         * SEMANTICS, MISO AND MOSI ARE STILL SIMULTANEOUSLY ACTIVE)
         * looks like this:
         * 
         * TX: ***|***|***|... |*  |
         * RX:    |***|***|... |*  |***
         *
         * The |*  | fragment is due to being unable to specify differing
         * amounts to read and write in the same command, which results in the 
         * ternary jumble below
         */
        case SPI_TRANSFER: {
            cmd_len = 
                (tx_complete) ?
                    MIN(cmd->len - driver_data.rx_progress, MIN_FIFO_DEPTH) :
                    MIN(cmd->len - driver_data.tx_progress, MIN_FIFO_DEPTH);
            spi_host_command = COMMAND_DIRECTION_BIDIRECTION;
            // Set RX watermark to interrupt at
            regs->CONTROL = (regs->CONTROL & ~CONTROL_RX_WATERMARK_MASK) | CONTROL_RX_WATERMARK(cmd->len);
            break;
        }
        default: {
            driver_data.err = SPI_ERR_INVALID_CMD;
            fsm_state.nxt_state = RESP;
            return;
        }
    }

    spi_host_command |= COMMAND_LEN_OFFSET(cmd_len); 
    sddf_printf("cmd=%x\n", spi_host_command);
    
    /* TODO: perhaps move everything beyond into SEL_CMD? */

    regs->COMMAND = spi_host_command; 

    void *write_buffer = (void *)
        driver_data.buffer_base + cmd->write_offset + driver_data.tx_progress;
    void *read_buffer = (void *)
        driver_data.buffer_base + cmd->read_offset + driver_data.rx_progress; 

    switch (cmd->mode) {
        case SPI_READ: {
            recieve_data(read_buffer, cmd_len);
            driver_data.rx_progress += cmd_len;
            fsm_state.yield = STATUS_RXQD(regs->STATUS) != cmd_len;
            break;
        }
        case SPI_WRITE: {
            transmit_data(write_buffer, cmd_len);
            driver_data.tx_progress += cmd_len;
            fsm_state.yield = STATUS_TXQD(regs->STATUS) != 0;
            break;
        }
        case SPI_TRANSFER: {
            // As noted above, this is meant to reflect the FIFO access pattern
            if (!tx_complete) {
                transmit_data(write_buffer, cmd_len);
                driver_data.tx_progress += cmd_len;
            }

            bool first = driver_data.tx_progress == 0;
            if (!first) {
                recieve_data(read_buffer, cmd_len);
                driver_data.rx_progress += cmd_len;
            }

            fsm_state.yield = (STATUS_RXQD(regs->STATUS) != cmd_len) || 
                              (STATUS_TXQD(regs->STATUS) != 0);

            break;
        }
        default: {
            driver_data.err = SPI_ERR_INVALID_CMD;
            fsm_state.nxt_state = RESP;
            break;
        }
    }

    fsm_state.nxt_state = CMD_RET;
}

void state_cmd_ret(void) { 
    spi_cmd_t *cmd = &driver_data.cmd[driver_data.cmd_in_progress];

    bool done = false;

    switch (cmd->mode) {
        case SPI_READ: {
            done = driver_data.rx_progress == cmd->len;
            break;
        }
        case SPI_WRITE: {
            done = driver_data.tx_progress == cmd->len;
            break;
        }
        case SPI_TRANSFER: {
            done = driver_data.rx_progress == cmd->len;
            break;
        }
        default: {
            driver_data.err = SPI_ERR_INVALID_CMD;
            fsm_state.nxt_state = RESP;
            break;
        }
    }

    if (done) {
        driver_data.cmd_in_progress++;
        fsm_state.nxt_state = SEL_CMD;
    }
    else {
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

    // Turn off SPI event interrupts, otherwise will be spammed with TXEMPTY
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

    // TODO: remove this
    uint32_t device_config =
        CONFIGOPTS_CLKDIV(0x7C) | 
        CONFIGOPTS_CSNIDLE(1) |
        CONFIGOPTS_CSNTRAIL(1) |
        CONFIGOPTS_CSNLEAD(1) |
        CONFIGOPTS_CPOL |
        CONFIGOPTS_CPHA;
    sddf_printf("config=%x\n", device_config);
    regs->CONFIGOPTS2 = device_config;

    queue_handle = spi_queue_init(config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr);

    microkit_dbg_puts("Driver initialised.\n");
}

char *fsm_str(spi_state_t state) {
    switch (state) {
        case IDLE: return "IDLE";
        case REQ: return "REQ";
        case SEL_CMD: return "SEL_CMD";
        case CMD: return "CMD";
        case CMD_RET: return "CMD_RET";
        case RESP: return "RESP";
        default: return "INVALID";
    }
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
                LOG_DRIVER("how did we end up here?");
            }
        }
        LOG_DRIVER("Exiting %s\n", fsm_str(state));
    } while (!fsm_state.yield);
    
    fsm_state.yield = false;
    return;
}

void notified(microkit_channel ch) {
    LOG_DRIVER("Notified on channel %d\n", ch);

    if (ch == 0) { // error 
        LOG_DRIVER("status=%8X error=%8X\n", regs->STATUS, regs->ERROR_STATUS);
        microkit_irq_ack(ch); 
    }
    else if (ch == 1) { // spi_event
        LOG_DRIVER("status=%8X error=%8X\n", regs->STATUS, regs->ERROR_STATUS);
        fsm();
        microkit_irq_ack(ch); 
    }
    else if (ch == 2) {
        fsm(); 
    }
    else {}
};
