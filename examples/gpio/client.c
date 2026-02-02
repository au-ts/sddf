

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <os/sddf.h>
#include <stdint.h>
#include <sddf/timer/config.h>
#include "include/client/client.h"
#include "include/motor/motor_control.h"
#include "include/client/timer_queue.h"
#include "include/ultrasonic/ultrasonic_sensor.h"

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_printf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define STACK_SIZE (4096)

// Channels
// #define TIMER_CHANNEL (1)
#define MOTOR_CONTROL_CHANNEL (2)
#define ULTRASONIC_CHANNEL (4)

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
static char t_client_main_stack[STACK_SIZE];

sddf_channel timer_channel;

uint64_t time_start;
uint64_t time_end;

cothread_t t_event;
cothread_t t_main;

PriorityQueue timeout_queue = {{}, {}, 0};

// Unfulfilled motor control request
int is_ongoing_request = 0;

bool delay_microsec(size_t microseconds, int timeout_id)
{
    size_t time_ns = microseconds * NS_IN_US;

    /* Detect potential overflow */
    if (microseconds != 0 && time_ns / microseconds != NS_IN_US) {
        LOG_CLIENT_ERR("overflow detected in delay_microsec\n");
        return false;
    }

    enqueue(&timeout_queue, sddf_timer_time_now(timer_channel) + microseconds, timeout_id);

    sddf_timer_set_timeout(timer_channel, time_ns);
    co_switch(t_event);

    return true;
}

bool delay_ms(size_t milliseconds, int timeout_id)
{
    size_t time_ns = milliseconds * NS_IN_MS;

    /* Detect potential overflow */
    if (milliseconds != 0 && time_ns / milliseconds != NS_IN_MS) {
        LOG_CLIENT_ERR("overflow detected in delay_ms\n");
        return false;
    }

    enqueue(&timeout_queue, sddf_timer_time_now(timer_channel) + milliseconds, timeout_id);

    sddf_timer_set_timeout(timer_channel, time_ns);
    co_switch(t_event);

    return true;
}

void delay_motors(size_t milliseconds) {
    delay_ms(milliseconds, MOTOR_CONTROL_TIMEOUT_ID);
}

uint64_t get_time_now() {
    return sddf_timer_time_now(timer_channel);
}

// send motor control request for micro_s micorseconds
void send_motor_request(int motor_ch, int command, uint64_t micro_s) {
    LOG_CLIENT("Sending motor request\n");

    microkit_msginfo new_msg = microkit_msginfo_new(0, 2);
    microkit_mr_set(0, command);
    microkit_mr_set(1, micro_s);

    microkit_ppcall(motor_ch, new_msg);
}

// returns distance in cm


// TODO check these
void drive_forward(uint64_t micro_s) {
    send_motor_request(MOTOR_CONTROL_CHANNEL, REQUEST_FORWARD, micro_s);
}

void drive_reverse(uint64_t micro_s) {
    send_motor_request(MOTOR_CONTROL_CHANNEL, REQUEST_BACK, micro_s);
}

void drive_left(uint64_t micro_s) {
    send_motor_request(MOTOR_CONTROL_CHANNEL, REQUEST_LEFT, micro_s);
}

void drive_right(uint64_t micro_s) {
    send_motor_request(MOTOR_CONTROL_CHANNEL, REQUEST_RIGHT, micro_s);
}

void drive_neutral(uint64_t micro_s) {
    send_motor_request(MOTOR_CONTROL_CHANNEL, REQUEST_NEUTRAL, micro_s);
}

void client_main(void) {
    // wait for all sensors to initialise first
    while (true)
    {
        // LOG_CLIENT("Client main\n");
        LOG_CLIENT("Reading received: %lu\n", get_ultrasonic_reading());
        delay_ms(1000, CLIENT_TIMEOUT_ID);
        control_forward();
        delay_motors(1000);
        control_reverse();

        // uint64_t averaged_dist = 0;
        // for (int i = 0; i < 3; i++) {
        //     uint64_t distance = get_ultrasonic_reading();
        //     if (!distance) {
        //         continue;
        //     }
        //     averaged_dist += distance;
        // }
        
        // averaged_dist /= 3;
        // // LOG_CLIENT("Sensor Reading Received: %ld\n", averaged_dist);

        // if (averaged_dist < 10) {
        //     drive_stop();
        //     // turn left every time there's an obstacle
        //     drive_left();
        //     delay_ms(4);
        // }
        // else {
        //     drive_forward();
        // }
        
        // time_end = sddf_timer_time_now(timer_channel);

        // LOG_CLIENT("Execution time: %ld\n", time_end - time_start);
    }
}

// Call coroutine, block other commands from executing
void notified(sddf_channel ch) {
    // check this switch
    if (ch == timer_config.driver_id) {
        int timeout_id = dequeue(&timeout_queue);

        switch (timeout_id)
        {
        case SENSOR_TIMEOUT_ID:
            co_switch(t_main);
            break;
        case CLIENT_TIMEOUT_ID:
            co_switch(t_main);
            break;
        case MOTOR_CONTROL_TIMEOUT_ID:
            handle_motor_control_timeout();
            break;
        case MOTOR_A_TIMEOUT_ID:
            handle_pwm_timeout(MOTOR_A_TIMEOUT_ID);
            break;
        case MOTOR_B_TIMEOUT_ID:
            handle_pwm_timeout(MOTOR_B_TIMEOUT_ID);
            break;        
        default:
            break;
        }
    }
    else {
        LOG_CLIENT("Unexpected channel call\n");
    }
}

void init(void) {
    sensor_init();
    motors_init();

    timer_channel = timer_config.driver_id;

    // time_start = sddf_timer_time_now(TIMER_CHANNEL);
    LOG_CLIENT("Init\n");

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

