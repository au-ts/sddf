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

    LOG_CLIENT("%d was recieved (err_cmd = %zu)\n", error, err_cmd);

    for (int i = 0; i < 8 /*change lol*/; i++)
        LOG_CLIENT("0x%x was recieved\n", buffer[0x800 + i]);
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

//TODO: remove after done testing
uint8_t tx_data[] = {
    0xFF, 0x00,
    0x2E, 0x2D,
    0x30, 0x2F,
    0x32, 0x31
};

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

    uint8_t *buffer = config.buffer.vaddr;

    for (int i = 0; i < sizeof(tx_data); i++)
        buffer[i] = tx_data[i];

    spi_cmd_t *spi_cmds = config.control.vaddr;
    spi_cmds[0] = (spi_cmd_t) {-1, 0, 1, SPI_WRITE};
    spi_cmds[1] = (spi_cmd_t) {0x0800, 1, sizeof(tx_data) - 1, SPI_TRANSFER};
    spi_cmds[2] = (spi_cmd_t) {0x0800 + sizeof(tx_data) - 1,  -1, 1, SPI_READ};

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
