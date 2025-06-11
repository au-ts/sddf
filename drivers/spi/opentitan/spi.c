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

volatile struct spi_regs *regs; 

// Driver state (for FSM?)
// TODO

// Shared memory regions
spi_queue_handle_t queue_handle;
uint8_t *buffer; // TODO: clarify why this isn't a struct?

static inline void spi_reset(void)
{
    // Reset SPI host
    regs->CONTROL = CONTROL_SW_RST;

    // Poll status until inactive and both FIFOs are drained
    uint32_t status = regs->STATUS; 
    while (STATUS_ACTIVE(status) || STATUS_TXQD(status) || STATUS_RXQD(status)) {
        status = regs->STATUS;
    }

    // Clear the reset bit
    regs->CONTROL = 0; 
}

static inline void spi_setup(void)
{
    spi_reset();

    // TODO: remove this
    regs->CONFIGOPTS2 = 0x7C;

    // Enable the device
    regs->CONTROL = CONTROL_SPIEN | CONTROL_OUTPUT_EN;

    // Poll status until the device is ready
    while (!STATUS_READY(regs->STATUS)) {} 
}

void init(void) {
    assert(spi_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);   
 
    regs = (volatile struct spi_regs *)device_resources.regions[0].region.vaddr;
    spi_setup(); 

    queue_handle = spi_queue_init(config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr);
    buffer = NULL;

    microkit_dbg_puts("Driver initialised.\n");
}

void transmit_data(uint8_t *buffer, uint16_t len) {
    volatile uint8_t  *TX_BYTE = (uint8_t *) &regs->TXDATA;

    // TODO: rewrite to support uint32_t writes
    for (uint16_t idx = 0; idx < len; idx++) {
        *TX_BYTE = buffer[idx];
    }
}

void recieve_data(uint8_t *buffer, uint16_t len) {
    // precondition: buffer and len is word-aligned, just to save implementation sanity
   
    uint32_t status;
    do {
        status = regs->STATUS;
        sddf_printf("status=%x\n", status);
    } while (STATUS_RXQD(status) != len);
 
    uint32_t *buffer_word = (uint32_t *) buffer;
    for (uint16_t idx = 0; idx < len / sizeof(uint32_t) + (len % sizeof(uint32_t)) ? 1 : 0; idx++) {
        buffer_word[idx] = regs->RXDATA;
        sddf_printf("%x was recieved\n", buffer_word[idx]);
    }
/*    uint8_t *buffer_tail = (uint8_t *)(buffer + len / sizeof(uint32_t));
    
    for (uint16_t idx = 0; idx < len % sizeof(uint32_t); idx++) {
        buffer_tail[idx] = 0; 
    }*/
}

void handle_request(void) {
    spi_cs_line_t cs_line;
    uintptr_t control_start_vaddr;
    uintptr_t buffer_base_vaddr;
    uint16_t len;

    int err = spi_dequeue_request(queue_handle, &cs_line, &control_start_vaddr,
        &buffer_base_vaddr, &len);

    if (err) {
        sddf_printf("error dequeueing request\n");
        return;
    }

    regs->CSID = cs_line;

    for (int cmd_idx = 0; cmd_idx < len; cmd_idx++) {
        spi_cmd_t *cmd = &((spi_cmd_t *) control_start_vaddr)[cmd_idx];

        uint32_t spi_host_command = COMMAND_LEN_OFFSET(cmd->len);
        if (cmd_idx < len - 1) // Not the last command
           spi_host_command |= COMMAND_CSAAT;

        uint8_t *buffer = (uint8_t *) buffer_base_vaddr + cmd->offset; 
        switch (cmd->mode) {
            case SPI_READ: {
                regs->COMMAND = spi_host_command | COMMAND_DIRECTION_RX_ONLY;
                sddf_printf("cmd=%x\n", spi_host_command);
                recieve_data(buffer, cmd->len);
                break;
            }
            case SPI_WRITE: {
                regs->COMMAND = spi_host_command | COMMAND_DIRECTION_TX_ONLY;
                sddf_printf("cmd=%x\n", spi_host_command);
                transmit_data(buffer, cmd->len);
                break;
            }
            case SPI_TRANSFER: {
                regs->COMMAND = spi_host_command | COMMAND_DIRECTION_BIDIRECTION;
                sddf_printf("cmd=%x\n", spi_host_command);
                transmit_data(buffer, cmd->len);
                recieve_data(buffer, cmd->len);
                break;
            }
            default: {
                sddf_printf("%x is an unsupported command", cmd->mode);
                break;
            }
        }
    }

    spi_enqueue_response(queue_handle, cs_line, 0, 0);
    microkit_deferred_notify(config.virt.id);
}

void notified(microkit_channel ch) {
    sddf_printf("driver: notified on channel %d\n", ch);

    if (ch == 0) {}
    else if (ch == 1) {}
    else if (ch == 2) {
        handle_request();
    }
    else {}
};
