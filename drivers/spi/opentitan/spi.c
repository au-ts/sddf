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

uintptr_t spi_host_regs;

volatile struct spi_regs *regs; 

static inline void spi_sw_reset(void)
{
    regs->CONTROL = CONTROL_SW_RST;
    regs->INTR_ENABLE = 0x0;
    LOG_DRIVER("clearing STATUS.ACTIVE\n");
    while (STATUS_ACTIVE(regs->STATUS)) {}
    LOG_DRIVER("waiting for TX FIFO to drain\n");
    while (STATUS_TXQD(regs->STATUS) != 0) {}
    LOG_DRIVER("waiting for RX FIFO to drain\n");
    while (STATUS_RXQD(regs->STATUS) != 0) {}
    LOG_DRIVER("clearing CONTROL.SW_RST\n");
    regs->CONTROL = 0; 
}

static inline void spi_setup(void)
{
    
}

void notified(microkit_channel ch) {
    sddf_printf("driver: notified on channel %d\n", ch);
};

void init() {
    LOG_DRIVER("Initializing driver\n");
    
    regs = (volatile struct spi_regs *)device_resources.regions[0].region.vaddr;

    spi_sw_reset();

    LOG_DRIVER("config=%x\n", regs->CONTROL);
    LOG_DRIVER("status=%x\n", regs->STATUS);

    // Test I can actually see anything
    regs->CSID = 2;
    regs->CONFIGOPTS2 = 0x0000007C;
    regs->CONTROL = CONTROL_SPIEN | CONTROL_OUTPUT_EN;

    for (uint32_t status = regs->STATUS; !STATUS_READY(status); status = regs->STATUS) {
        LOG_DRIVER("regs->STATUS=%x, STATUS_READY=%lx\n", status, STATUS_READY(status));
    }

    uint32_t length = 64;

    while (true) {
        LOG_DRIVER("iterating\n");
        for (uint32_t status = regs->STATUS; !STATUS_READY(status); status = regs->STATUS) {
            LOG_DRIVER("regs->STATUS=%x, STATUS_READY=%lx\n", status, STATUS_READY(status));
        } 
        
        regs->CSID = 2;
        LOG_DRIVER("CSID set, CSID=%x\n", regs->CSID);
        
        regs->COMMAND = COMMAND_DIRECTION_BIDIRECTION | COMMAND_LEN_OFFSET(length);  
        LOG_DRIVER("command sent, status=%x\n", regs->STATUS);
 
        for (int i = 0; i < length / 4; i++) {
            regs->TXDATA =
                (i * 4 + 0) << 24 |
                (i * 4 + 1) << 16 |
                (i * 4 + 2) <<  8 |
                (i * 4 + 3) <<  0;
            uint32_t status = regs->STATUS;
            LOG_DRIVER("TX FIFO has %d words in it, status of %x\n", STATUS_TXQD(status), status);
        }
       
        uint32_t status = regs->STATUS;
        do { 
            LOG_DRIVER("RX FIFO has %d words in it, status=%x\n", STATUS_RXQD(status), status);
            for (volatile int i = 0; i < 0x1000; i++) {
                volatile int j = i;
                i = i & j;
            }
            status = regs->STATUS;
        } while (STATUS_RXQD(status) != length / 4);

        for (int i = 0; i < length / 4; i++) {
            LOG_DRIVER("word %d = %x\n", i, regs->RXDATA);
        }
    }
}
