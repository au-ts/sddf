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

#define VIRT 0

uintptr_t meta = 0x10000000, 
          data = 0x10001000;

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

    LOG_CLIENT("%d was recieved\n", error);
    spi_enqueue_request(handle, 0, 0, 0, 0);
    if (error < 64)
        microkit_deferred_notify(VIRT);        
}

void notified(microkit_channel ch) {
    switch (ch) {
        case VIRT: {
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

    microkit_msginfo claim = microkit_msginfo_new(SPI_BUS_CLAIM, 1);
    microkit_mr_set(SPI_BUS_SLOT, 0);
    microkit_msginfo ret = microkit_ppcall(VIRT, claim);
    LOG_CLIENT("ppc returned %lu\n", microkit_msginfo_get_label(ret));

    handle = spi_queue_init(
        (spi_request_queue_t *) meta, 
        (spi_response_queue_t *) meta + sizeof(spi_request_queue_t)
    );

    // Do initial operation
    spi_enqueue_request(handle, 0, 0, 0, 0);

    microkit_deferred_notify(VIRT);
    
    LOG_CLIENT("sent request off\n");
}
