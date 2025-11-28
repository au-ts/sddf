/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/client.h>
#include <sddf/i2c/config.h>
#include <sddf/i2c/libi2c.h>

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("SCAN|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("SCAN|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

bool delay_ms(size_t milliseconds);

__attribute__((__section__(".i2c_client_config"))) i2c_client_config_t i2c_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

static serial_queue_handle_t serial_tx_queue_handle;

i2c_queue_handle_t queue;
uintptr_t data_region;
libi2c_conf_t libi2c_conf;

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

#ifndef I2C_DATA_REGION
#define I2C_DATA_REGION ((uint8_t *)i2c_config.data.vaddr)
#endif

void client_main(void)
{
    LOG_CLIENT("client_main: started\n");
    while (true) {
        // Try probe all addresses
        uint8_t *data = (uint8_t *)data_region;
        data[0] = 0;
        sddf_printf("SCAN|SCAN: Beginning scan...\n");
        for (uint8_t i = 1; i < (1 << 7); i++) {
            sddf_printf("SCAN|SCAN: \t address 0x%X", i);
            int ret = sddf_i2c_write(&libi2c_conf, i, data, 1);
            if (ret == 0) {
                sddf_printf("\n           \t ... is present!\n");
            } else {
                sddf_printf(" not detected.\n");
            }
        }
        sddf_printf("\nRescanning in 5 seconds...\n");
        delay_ms(5000);
    }
}

bool delay_ms(size_t milliseconds)
{
    size_t time_ns = milliseconds * NS_IN_MS;

    /* Detect potential overflow */
    if (milliseconds != 0 && time_ns / milliseconds != NS_IN_MS) {
        LOG_CLIENT_ERR("overflow detected in delay_ms");
        return false;
    }

    sddf_timer_set_timeout(timer_config.driver_id, time_ns);
    co_switch(t_event);

    return true;
}

void init(void)
{
    assert(serial_config_check_magic(&serial_config));
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

    sddf_printf("SCAN|INFO: init\n");

    assert(i2c_config_check_magic((void *)&i2c_config));

    data_region = (uintptr_t)i2c_config.data.vaddr;
    queue = i2c_queue_init(i2c_config.virt.req_queue.vaddr, i2c_config.virt.resp_queue.vaddr);

    // Claim all addresses except the general call address (0)
    for (uint8_t i = 1; i < (1 << 7); i++) {
        bool claimed = i2c_bus_claim(i2c_config.virt.id, i);
        if (!claimed) {
            LOG_CLIENT_ERR("failed to claim %u!\n", i);
            return;
        }
        LOG_CLIENT("claimed peripheral address %u\n", i);
    }

    /* Initialise libi2c */
    libi2c_init(&libi2c_conf, &queue);

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

void notified(microkit_channel ch)
{
    if (ch == i2c_config.virt.id || ch == timer_config.driver_id) {
        co_switch(t_main);
    } else if (ch == serial_config.tx.id) {
        // Nothing to do
    } else {
        LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}
