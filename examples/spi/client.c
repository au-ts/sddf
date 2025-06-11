/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/spi/client.h>
#include <sddf/spi/config.h>
#include <sddf/util/printf.h>

//TODO: replace with libspi header once written 
#include <sddf/spi/queue.h>

__attribute__((__section__(".spi_client_config"))) spi_client_config_t config;

#define DEBUG_CLIENT
#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("SPI_CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("SPI_CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

spi_queue_handle_t handle;

static inline void handle_response() {
    spi_cs_line_t cs_line;
    spi_err_t error;
    size_t err_cmd;

    int err = spi_dequeue_response(handle, &cs_line, &error, &err_cmd);
    if (err) {
        LOG_CLIENT_ERR("dead\n");
        return;
    }

    uint8_t *buffer = config.buffer.vaddr;

    LOG_CLIENT("%d was recieved\n", error);

    LOG_CLIENT("0x%x was recieved\n", buffer[8]);

    while (true) {}
}

void notified(microkit_channel ch) {
    switch (ch) {
        //TODO: should be config.virt.id but not constexpr :(
        case 0: {
            handle_response();
            break;
        }
        default: {
            LOG_CLIENT_ERR("Spuriously notified on %d\n", ch);
            break;
        }
    }
}

void init(void) {
    LOG_CLIENT("initializing\n");

    handle = spi_queue_init(
        config.virt.req_queue.vaddr,
        config.virt.resp_queue.vaddr 
    );
    
    // Test to see if plumbing works
    // Claim bus 2
    microkit_msginfo claim = microkit_msginfo_new(SPI_BUS_CLAIM, 1);
    microkit_mr_set(SPI_BUS_SLOT, 2);
    microkit_msginfo ret = microkit_ppcall(config.virt.id, claim);
    LOG_CLIENT("ppc returned %lu\n", microkit_msginfo_get_label(ret));

    spi_cmd_t *spi_cmds = config.control.vaddr;
    spi_cmds[0] = (spi_cmd_t) {0, 2, SPI_WRITE}; // Switch to bank 0
    spi_cmds[1] = (spi_cmd_t) {4, 1, SPI_WRITE}; // Request WHO_AM_I
    spi_cmds[2] = (spi_cmd_t) {8, 1, SPI_READ};  // Recieve WHO_AM_I

    uint8_t *buffer = config.buffer.vaddr;
    buffer[0] = BIT(7) | 0x7F; 
    buffer[1] = 0;
    buffer[4] = 0;

    // Do initial operation
    spi_enqueue_request(
        handle, 
        2, 
        (uintptr_t) config.control.vaddr, 
        (uintptr_t) config.buffer.vaddr, 
        3
    );

    microkit_deferred_notify(config.virt.id);
    
    LOG_CLIENT("sent request off\n");
}
