/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <libco.h>
#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>
#include <sddf/util/printf.h>
#include <sddf/pmic/client.h>
#ifdef CONFIG_PLAT_MAAXBOARD
#include <sddf/pmic/bd71837amwv-bindings.h>
#define TARGET_REGULATOR (BD718XX_BUCK2)    // VDD_ARM
#define VOLTAGE_A   (900000)    // 0.9V
#define VOLTAGE_B   (1000000)   // 1V
#else
#error "Unsupported board!"
#endif

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

cothread_t t_event;
cothread_t t_main;

static serial_queue_handle_t serial_tx_queue_handle;

// TODO: sdfgen for pmic client channel
#define PMIC_CHANNEL (0)

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("SCAN|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("SCAN|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

static inline bool delay_ms(size_t milliseconds)
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

sddf_channel timer_channel;

void notified(sddf_channel ch)
{
    if (ch == timer_config.driver_id) {
        co_switch(t_main);
    } else if (ch == serial_config.tx.id) {
        // nothing to do
    } else {
        LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}

void client_main(void) {
    LOG_CLIENT("Entered main loop.\n");
    for (uint32_t i = 0;; i++) {
        // Alternate between setting voltage rail to 0.9 or 1V
        if (i % 2) {
            sddf_pmic_set_vout(PMIC_CHANNEL, TARGET_REGULATOR, VOLTAGE_A);
            LOG_CLIENT("Set voltage of regulator %d to %zu\n", TARGET_REGULATOR, VOLTAGE_A);
        } else {
            sddf_pmic_set_vout(PMIC_CHANNEL, TARGET_REGULATOR, VOLTAGE_B);
            LOG_CLIENT("Set voltage of regulator %d to %zu\n", TARGET_REGULATOR, VOLTAGE_B);
        }
        delay_ms(5000);
    }
}

void init(void)
{
    assert(serial_config_check_magic(&serial_config));
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

    assert(timer_config_check_magic(&timer_config));
    sddf_printf("CLIENT|INFO: starting\n");

    timer_channel = timer_config.driver_id;

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}
