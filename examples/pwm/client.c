/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/util/printf.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/pwm/client.h>

static serial_queue_handle_t serial_tx_queue_handle;
__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

#define LOG_CLIENT(...) do{ sddf_printf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define CH_PWM_CONTROL_PPC 0

void init(void)
{
    assert(serial_config_check_magic(&serial_config));
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

    for (volatile int i = 0; i < 1000000; i++) {}

    LOG_CLIENT("starting\n");

    bool success = sddf_pwm_set_ns(CH_PWM_CONTROL_PPC, 0, /* period ns */ 500, /* pulse width ns */ 200, 0);
    assert(success);

    LOG_CLIENT("done\n");
}

void notified(sddf_channel ch)
{
    if (ch == serial_config.tx.id) {
        // Nothing to do.
    } else {
        LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}
