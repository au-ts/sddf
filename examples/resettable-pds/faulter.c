/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/util/printf.h>

#include "faulter_data.h"

// __attribute__((__section__(".serial_client_config"))) serial_client_config_t config;

// serial_queue_handle_t rx_queue_handle;
// serial_queue_handle_t tx_queue_handle;

int my_global = 3;

int my_zero = 0;

uint8_t big_data[1024 * 32];

void init(void)
{
    // serial_config_check_magic(&config);

    // serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    // serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);

    // serial_putchar_init(config.tx.id, &tx_queue_handle);
    // sddf_printf("FAULTER|INFO: starting\n");

    microkit_dbg_puts("FAULTER|INFO: starting\n");

    if (my_global == 3) {
        microkit_dbg_puts("FAULTER|INFO: my_global is 3.\n");
    } else {
        microkit_dbg_puts("FAULTER|ERROR: my_global is unexpected.\n");
    }

    if (my_zero == 0) {
        microkit_dbg_puts("FAULTER|INFO: my_zero is 0.\n");
    } else {
        microkit_dbg_puts("FAULTER|ERROR: my_zero is unexpected.\n");
    }

    my_global = 4;
    my_zero = 10;

    if (my_global == 4) {
        microkit_dbg_puts("FAULTER|INFO: my_global is 4.\n");
    } else {
        microkit_dbg_puts("FAULTER|ERROR: my_global is unexpected.\n");
    }

    if (my_zero == 10) {
        microkit_dbg_puts("FAULTER|INFO: my_zero is 10.\n");
    } else {
        microkit_dbg_puts("FAULTER|ERROR: my_zero is unexpected.\n");
    }

    // sddf_printf("FAULTER|INFO: faulting\n");
    microkit_internal_crash(0);
}

void notified(microkit_channel ch)
{
}
