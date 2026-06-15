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
#include <sddf/tmu/client.h>

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

cothread_t t_event;
cothread_t t_main;

static serial_queue_handle_t serial_tx_queue_handle;

// TODO: sdfgen for tmu client channel
#define TMU_CHANNEL (0)

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("TMU_CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("TMU_CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

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
    } else if (ch == TMU_CHANNEL) {
        LOG_CLIENT_ERR("Warning: IRQ forwarded!\n");
    } else {
        LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}

static uint64_t busywork_magic = 0;

void client_main(void) {
    LOG_CLIENT("Entered main loop.\n");
    int ret;
    #ifdef SDDF_PMU_ENABLE_IRQ
    // Set an average temperature IRQ forward @ 45 deg C
    int ret = sddf_tmu_set_irq_mode(TMU_CHANNEL, SDDF_TMU_IRQ_MODE_AVG);
    assert(!ret);
    ret = sddf_tmu_set_irq_threshold(TMU_CHANNEL, 45.0);
    assert(!ret);
    #endif

    sddf_tmu_temp_info_t temp_info;
    for (;;) {
        // Get temperature and print
        ret = sddf_tmu_get_temp(TMU_CHANNEL, &temp_info);
        if (ret) {
            LOG_CLIENT_ERR("Failed to get temperature!\n");
        } else {
            LOG_CLIENT("\n\nRead successfully!\n");
            LOG_CLIENT("\tAvg. valid: %d\n", temp_info.valid_avg);
            LOG_CLIENT("\tAvg. temp: %f\n", temp_info.temp_avg);
            LOG_CLIENT("\tInst. valid: %d\n", temp_info.valid_inst);
            LOG_CLIENT("\tInst. temp: %f\n", temp_info.temp_inst);
        }
        // delay_ms(2000);
        // Busy wait to make heat
        for (uint64_t i = 0; i < 100000000; i++) {
            busywork_magic++;
            busywork_magic = ((busywork_magic / 2) << 3) - 5;
            busywork_magic = (busywork_magic * busywork_magic) + 300;
            if (busywork_magic < 500) {
                busywork_magic = busywork_magic * 718;
            } else {
                busywork_magic = busywork_magic - (300*busywork_magic);
            }
        }
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
