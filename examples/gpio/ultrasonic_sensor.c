

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/gpio/meson/gpio.h>
#include "include/client/client.h"
#include "gpio_config.h"

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define  LOG_SENSOR(...) do{}while(0)
// #define LOG_SENSOR(...) do{ sddf_printf("SENSOR|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define  LOG_SENSOR(...) do{}while(0)
#endif

#define LOG_SENSOR_ERR(...) do{ sddf_printf("SENSOR|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// uintptr_t ultrasonic_input_buffer_base_vaddr;
// uintptr_t ultrasonic_output_buffer_base_vaddr;

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_sensor_main_stack[STACK_SIZE];

// Channels
#define CLIENT_CHANNEL (1)
#define TIMER_CHANNEL (2)

#define GPIO_CHANNEL_ECHO (3)
#define GPIO_CHANNEL_TRIG (4)

#define GPIO_HIGH (1)
#define GPIO_LOW (0)

// Timer States for PWM
#define PAUSE_HIGH (0)
#define PAUSE_LOW (1)

// Time (ms) Timeout for Sensor Read
#define SENSOR_TIMEOUT (38)


uint64_t curr_dist = 0;

void gpio_init(int gpio_ch, int direction) {
    microkit_msginfo msginfo;
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_DIRECTION);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, direction);
    msginfo = microkit_ppcall(gpio_ch, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_SENSOR_ERR("failed to set direction of gpio with error %ld!\n", error);
        while (1) {};
    }
}

// GPIO output HIGH/LOW
void digital_write(int gpio_ch, int value) {
    microkit_msginfo msginfo;
    if (value == GPIO_HIGH) {
        // LOG_CONTROL("Setting GPIO1 to on!\n");
        msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
        microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
        microkit_mr_set(GPIO_REQ_VALUE_SLOT, 1);
        msginfo = microkit_ppcall(gpio_ch, msginfo);
        if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
            size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
            LOG_SENSOR_ERR("failed to set output of gpio with error %ld!\n", error);
            while (1) {};
        }       
    }
    else if (value == GPIO_LOW) {
        // TODO check if this is correct to set GPIO LOW
        // LOG_CONTROL("Setting GPIO1 to off!\n");
        msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
        microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
        microkit_mr_set(GPIO_REQ_VALUE_SLOT, 0);
        msginfo = microkit_ppcall(gpio_ch, msginfo);
        if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
            size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
            LOG_SENSOR_ERR("failed to set output of gpio with error %ld!\n", error);
            while (1) {};
        }
    }
}

bool delay_microsec(size_t microsec)
{
    size_t time_us = microsec * NS_IN_US;

    /* Detect potential overflow */
    if (microsec != 0 && time_us / microsec != NS_IN_US) {
        LOG_SENSOR_ERR("overflow detected in delay_microsec\n");
        return false;
    }

    sddf_timer_set_timeout(TIMER_CHANNEL, time_us);
    co_switch(t_event);

    return true;
}

// Read duration of value from GPIO pin (in micro seconds)
uint64_t pulse_in(int gpio_ch, int value) {
    uint64_t time_start = sddf_timer_time_now(TIMER_CHANNEL);
    uint64_t time_received = 0;
    uint64_t time_change = 0;
    int has_received = 0;

    while (true) {
        // LOG_SENSOR("sensor read attempt\n");

        microkit_msginfo msginfo;
        msginfo = microkit_msginfo_new(GPIO_GET_GPIO, 1);
        microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_INPUT);
        msginfo = microkit_ppcall(gpio_ch, msginfo);
        if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
            size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
            LOG_SENSOR_ERR("failed to get input of gpio with error %ld!\n", error);
            while (1) {};
        }

        int value_received = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        if (value_received == value) {
            // First time measured value has been received
            if (!has_received) {
                has_received = 1;
                time_received = sddf_timer_time_now(TIMER_CHANNEL);
                continue;
            }

            uint64_t time_now = sddf_timer_time_now(TIMER_CHANNEL);

            if (((time_now - time_start) / NS_IN_MS) > SENSOR_TIMEOUT) {
                return 0;
            }

        } 
        else {
            // Timeout not seeing GPIO HIGH from sensor
            uint64_t time_now = sddf_timer_time_now(TIMER_CHANNEL);
            if (((time_now - time_start) / NS_IN_MS) > (SENSOR_TIMEOUT * 100)) {
                return 0;
            }

            // Have received measured value before, this is time when value changes
            if (has_received) {
                time_change = sddf_timer_time_now(TIMER_CHANNEL);
                break;
            }
        }
    }

    if (time_change && time_received) {
        // micro seconds
        return (time_change - time_received) / 1000;
    }

    return 0;
}

void sensor_main(void) {
    LOG_SENSOR("init\n");
    gpio_init(GPIO_CHANNEL_ECHO, GPIO_DIRECTION_INPUT);
    gpio_init(GPIO_CHANNEL_TRIG, GPIO_DIRECTION_OUTPUT);

    delay_microsec(2);
    // LOG_SENSOR("attempt reading\n");

    while (true) {
        digital_write(GPIO_CHANNEL_TRIG, GPIO_LOW);
        delay_microsec(2);

        digital_write(GPIO_CHANNEL_TRIG, GPIO_HIGH);
        delay_microsec(10);

        digital_write(GPIO_CHANNEL_TRIG, GPIO_LOW);

        uint64_t duration = pulse_in(GPIO_CHANNEL_ECHO, GPIO_HIGH);
        if (duration) {
            uint64_t distance = duration * 0.034 / 2;
            curr_dist = distance;
            
            LOG_SENSOR("distance received, %ld\n", distance);
        } else {
            curr_dist = 0;
        }
        
        LOG_SENSOR("done reading\n");
        delay_microsec(1000000);
    }   
}

// TODO: might want to buffer over multiple reads
uint64_t read_sensor() {
    digital_write(GPIO_CHANNEL_TRIG, GPIO_LOW);
    delay_microsec(2);

    digital_write(GPIO_CHANNEL_TRIG, GPIO_HIGH);
    delay_microsec(10);

    uint64_t duration = pulse_in(GPIO_CHANNEL_ECHO, GPIO_HIGH);
    if (duration) {
        uint64_t distance = duration * 0.034 / 2;
        LOG_SENSOR("Sensor Reading Received: %ld\n", distance);
        return distance;
    }  
    
    return 0;
}

microkit_msginfo send_reading_to_client() {
    uint64_t distance = curr_dist;

    microkit_msginfo new_msg = microkit_msginfo_new(0, 1);

    microkit_mr_set(0, distance);

    return new_msg;
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo) {
    switch (ch) {
    case CLIENT_CHANNEL:
        // co_switch(t_main);
        LOG_SENSOR("Client call\n");
        microkit_msginfo res = send_reading_to_client();
        return res;
        break;
    default:
        LOG_SENSOR("Unexpected pp call\n");
        break;
    }

    microkit_msginfo res = microkit_msginfo_new(0, 0);
    return res;
}

void notified(microkit_channel ch) {
    switch (ch)
    {
    case TIMER_CHANNEL:
        co_switch(t_main);
        break;
    default:
        LOG_SENSOR("Unexpected channel call\n");
        break;
    }
}


void init(void) {
    LOG_SENSOR("Init\n");
    // sensor_main();

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_sensor_main_stack, STACK_SIZE, sensor_main);

    co_switch(t_main);
}

