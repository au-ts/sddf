

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "include/client/client.h"

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_printf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define STACK_SIZE (4096)


__attribute__((__section__(".gpio_client_config"))) gpio_client_config_t gpio_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;


static char t_client_main_stack[STACK_SIZE];

uint64_t time_start;
uint64_t time_end;

cothread_t t_event;
cothread_t t_main;

PriorityQueue timeout_queue = {{}, {}, 0};

// Note: not the actual value for these channels, actual channel ids are set by driver_id in client init()
sddf_channel timer_channel = 0;

// Ultrasonic GPIO channels
sddf_channel gpio_channel_echo_a = 0;
sddf_channel gpio_channel_trigger_a = 0;

sddf_channel gpio_channel_echo_b = 0;
sddf_channel gpio_channel_trigger_b = 0;

sddf_channel gpio_channel_echo_c = 0;
sddf_channel gpio_channel_trigger_c = 0;

// Motor GPIO channels
sddf_channel gpio_channel_motor_a = 0;
sddf_channel gpio_channel_motor_b = 0;

bool delay_microseconds(size_t microseconds, int timeout_id)
{
    size_t time_ns = microseconds * NS_IN_US;

    /* Detect potential overflow */
    if (microseconds != 0 && time_ns / microseconds != NS_IN_US) {
        LOG_CLIENT_ERR("overflow detected in delay_microsec\n");
        return false;
    }

    enqueue(&timeout_queue, sddf_timer_time_now(timer_channel) + time_ns, timeout_id);

    sddf_timer_set_timeout(timer_channel, time_ns);
    co_switch(t_event);

    return true;
}

bool delay_miliseconds(size_t milliseconds, int timeout_id)
{
    size_t time_ns = milliseconds * NS_IN_MS;

    /* Detect potential overflow */
    if (milliseconds != 0 && time_ns / milliseconds != NS_IN_MS) {
        LOG_CLIENT_ERR("overflow detected in delay_ms\n");
        return false;
    }

    enqueue(&timeout_queue, sddf_timer_time_now(timer_channel) + time_ns, timeout_id);

    sddf_timer_set_timeout(timer_channel, time_ns);
    co_switch(t_event);

    return true;
}

void set_timeout(uint64_t microseconds) {
    sddf_timer_set_timeout(timer_channel, microseconds*NS_IN_US);
}

uint64_t get_time_now() {
    return sddf_timer_time_now(timer_channel);
}

// returns distance in cm

void client_main(void) {
    // wait for all sensors to initialise first
    // control_forward();

    // time_start = sddf_timer_time_now(timer_channel);
    // digital_write(gpio_channel_echo_a, GPIO_LOW);

    // control_forward();


    while(true)
    {
        // sensor a: right
        // sensor b: forward
        // sensor c: left

        uint64_t dist_sensor_a = get_ultrasonic_reading(gpio_channel_echo_a, gpio_channel_trigger_a);
        uint64_t dist_sensor_b = get_ultrasonic_reading(gpio_channel_echo_b, gpio_channel_trigger_b);
        uint64_t dist_sensor_c = get_ultrasonic_reading(gpio_channel_echo_c, gpio_channel_trigger_c);

        // LOG_CLIENT("dist sensor a: %lu\n", dist_sensor_a);
        // LOG_CLIENT("dist sensor b: %lu\n", dist_sensor_b);
        // LOG_CLIENT("dist sensor c: %lu\n", dist_sensor_c);
        
        if (dist_sensor_b > 40 && dist_sensor_a > 40 && dist_sensor_c > 40) {
            LOG_CLIENT("attempting drive\n");
            control_forward();
            LOG_CLIENT("returned from drive\n");
        }
        else {
            control_stop();
            if (dist_sensor_a > dist_sensor_c) {
                control_right();
            }
            else {
                control_left();
            }
        }
    }
}

// Call coroutine, block other commands from executing
void notified(sddf_channel ch) {
    // check this switch
    // LOG_CLIENT("timer: %d\n", ch);

    if (ch == timer_channel) {
        int timeout_id = dequeue(&timeout_queue);
        // LOG_CLIENT("timeout now\n");
        // LOG_CLIENT("timeout id: %d\n", timeout_id);

        // TODO: horrible style, refactor this and how timeouts are handled (especially for motors)
        if (timeout_id == SENSOR_TIMEOUT_ID) {
            // LOG_CLIENT("sensor timeout\n");
            co_switch(t_main);
        }
        else if (timeout_id == CLIENT_TIMEOUT_ID) {
            // LOG_CLIENT("client timeout\n");
            co_switch(t_main);
        }
    }
    else {
        LOG_CLIENT("Unexpected channel call\n");
    }
}

void init(void) {
    timer_channel = timer_config.driver_id;

    // TODO: these arent used anymore as we now have a PWM driver, remove these
    // Motor GPIO channels
    gpio_channel_motor_a = gpio_config.driver_channel_ids[0];
    gpio_channel_motor_b = gpio_config.driver_channel_ids[1];

    // Ultrasonic channels
    gpio_channel_echo_a = gpio_config.driver_channel_ids[2];
    gpio_channel_trigger_a = gpio_config.driver_channel_ids[3];

    LOG_CLIENT("echo: %d\n", gpio_channel_echo_a);
    LOG_CLIENT("trigger: %d\n", gpio_channel_trigger_a);

    gpio_channel_echo_b = gpio_config.driver_channel_ids[4];
    gpio_channel_trigger_b = gpio_config.driver_channel_ids[5];

    gpio_channel_echo_c = gpio_config.driver_channel_ids[6];
    gpio_channel_trigger_c = gpio_config.driver_channel_ids[7];

    sensor_init(gpio_channel_echo_a, gpio_channel_trigger_a);
    sensor_init(gpio_channel_echo_b, gpio_channel_trigger_b);
    sensor_init(gpio_channel_echo_c, gpio_channel_trigger_c);


    // client_main();
    LOG_CLIENT("Init\n");

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);
    
    co_switch(t_main);
}

