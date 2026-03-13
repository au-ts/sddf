/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/serial/config.h>

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;
static serial_queue_handle_t serial_tx_queue_handle;

#define DEBUG_CLIENT
#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("WORKER|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("WORKER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

void notified(sddf_channel ch)
{
    if (ch == serial_config.tx.id) {
        // nothing to do
    } else {
        LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}

volatile uint64_t work_unit = 0;

void init(void)
{
    assert(serial_config_check_magic(&serial_config));
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

    LOG_CLIENT("starting...");

    // Busy work it up
    while (1) {
        if (work_unit == 0) {
            work_unit = work_unit - 777;
            continue;
        }
        work_unit = work_unit / 3;
        work_unit <<= (work_unit * 3);
        work_unit++;
    }

}

