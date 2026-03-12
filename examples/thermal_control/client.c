/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/clk/client.h>
#include <sddf/serial/config.h>
#include <sddf/timer/config.h>
#include <sddf/dvfs/client.h>
#include <sddf/dvfs/protocol.h>
#include <sddf/tmu/client.h>
#include <sddf/pwm/client.h>
#include "thermal_control.h"

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;
static serial_queue_handle_t serial_tx_queue_handle;

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

// TODO: sdfgen for channels
#define DVFS_CHANNEL (0)
#define PWM_CONTROL_CHANNEL (1)
#define TMU_CHANNEL (2)
sddf_channel timer_channel;

#define PWM_FAN_CHANNEL_ID (1) // NOT A MICROKIT CHANNEL!

#define DEBUG_CLIENT
#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("THERMAL|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("THERMAL|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// Trip point table
// TODO: abstract for other boards
// invariant: sorted in order of temp bound
#define NUM_TRIP_POINTS (7)
trip_point_t tp_table[NUM_TRIP_POINTS] = {
    {
        .temp_lower_bound = 20.0,
        .dvfs_opp = 3,  // Max power for Maaxboard
        .fan_pwm_duty = 5,
    },
    {
        .temp_lower_bound = 40.0,
        .dvfs_opp = 3,  // Max power for Maaxboard
        .fan_pwm_duty = 30,
    },
    {
        .temp_lower_bound = 60.0,
        .dvfs_opp = 3,  // Max power for Maaxboard
        .fan_pwm_duty = 70,
    },
    {
        .temp_lower_bound = 65.0,   // optimistic stable point
        .dvfs_opp = 3,  // Max power for Maaxboard
        .fan_pwm_duty = 100,
    },
    {
        .temp_lower_bound = 80.0,
        .dvfs_opp = 2,  // begin to throttle as we approach sensor max (85)
        .fan_pwm_duty = 100,
    },
    {
        .temp_lower_bound = 82.0,
        .dvfs_opp = 1,  // throttle more
        .fan_pwm_duty = 100,
    },
    {
        .temp_lower_bound = 84.0,
        .dvfs_opp = 0,  // max throttle
        .fan_pwm_duty = 100,
    }
};


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

static inline trip_point_t *get_trip_point(sddf_temp_celsius_t temp) {
    trip_point_t *ret;
    for (int i = 0; i < NUM_TRIP_POINTS; i++) {
        ret = &tp_table[i];
        if (ret->temp_lower_bound >= temp) {
            break;
        }
    }
    return ret;
}


/**
 * Thermal management loop.
 *
 * Each cycle:
 *  a. Check current system temperature using TMU
 *  b. Set DVFS operating point to appropriate level for temp
 *  c. Set fan PWM to appropriate level for temp
 *  d. Wait and loop
 */
void client_main(void) {

    sddf_tmu_temp_info_t temp_info;
    trip_point_t *prev_tp = &tp_table[0];
    for(uint64_t i;;i++) {
        LOG_CLIENT("\n\nPolling...\n");
        // get temp
        sddf_tmu_err_t ret = sddf_tmu_get_temp(TMU_CHANNEL, &temp_info);
        if (ret) {
            LOG_CLIENT_ERR("Failed to get temperature!\n");
            assert(false);
        } else {
            LOG_CLIENT("\tTemperature readout:\n");
            LOG_CLIENT("\t\tInst. valid: %d\n", temp_info.valid_inst);
            LOG_CLIENT("\t\tInst. temp: %f\n", temp_info.temp_inst);
        }

        trip_point_t *tp = get_trip_point(temp_info.temp_inst);
        if (tp != prev_tp) {
            LOG_CLIENT("\tNew trip point:\n");
            LOG_CLIENT("\t\tLower temp. bound: %f\n", tp->temp_lower_bound);
            LOG_CLIENT("\t\tOperating point idx: %zu\n", tp->dvfs_opp);
            LOG_CLIENT("\t\tFan power: %zu\n", tp->fan_pwm_duty);
        }
        prev_tp = tp;

        // set dvfs operating point
        int ret1 = sddf_dvfs_set_point(DVFS_CHANNEL, 0, tp->dvfs_opp);
        if (ret1 != SDDF_DVFS_SUCCESS) {
            LOG_CLIENT_ERR("Fail to get OPP, Error: %d\n", ret1);
            assert(false);
        }

        // set fan speed
        bool success = sddf_pwm_set_freq_duty(PWM_CONTROL_CHANNEL, PWM_FAN_CHANNEL_ID , FAN_FREQ, tp->fan_pwm_duty, 0);
        if (!success) {
            LOG_CLIENT_ERR("Failed to set fan PWM speed!");
            assert(false);
        }
        LOG_CLIENT("Sleeping until next poll...\n");
        if (i % 2) {
            LOG_CLIENT("tick\n");
        } else {
            LOG_CLIENT("tock\n");
        }
        // finally, sleep
        delay_ms(2000);
    }
}


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
