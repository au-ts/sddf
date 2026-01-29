

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
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

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
sddf_channel timer_channel;

cothread_t t_event;
cothread_t t_main;

// Channels
#define CLIENT_CHANNEL (1)
// #define TIMER_CHANNEL (2)

#define GPIO_CHANNEL_ECHO (3)
#define GPIO_CHANNEL_TRIG (4)

#define GPIO_HIGH (1)
#define GPIO_LOW (0)

// Timer States for TRIG pin
#define TRIG_UNSET (0)
#define TRIG_HIGH (1)
#define TRIG_LOW (2)

// Timer states for timeout
#define RUNNING (0)
#define TIMED_OUT (1)

// Time (ms) Timeout for Sensor Read
#define SENSOR_TIMEOUT (38)

int trig_state = TRIG_UNSET;
int timeout_state = RUNNING;

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

bool timeout_microsec(size_t microsec)
{
    size_t time_us = microsec * NS_IN_US;
    /* Detect potential overflow */
    if (microsec != 0 && time_us / microsec != NS_IN_US) {
        LOG_SENSOR_ERR("overflow detected in timeout_microsec\n");
        return false;
    }
    sddf_timer_set_timeout(timer_channel, microsec);
    return true;
}

// Read duration of value from GPIO pin (in micro seconds)
uint64_t pulse_in(int gpio_ch, int value) {
    uint64_t time_start = sddf_timer_time_now(timer_channel);
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
                time_received = sddf_timer_time_now(timer_channel);
                continue;
            }

            uint64_t time_now = sddf_timer_time_now(timer_channel);

            if (((time_now - time_start) / NS_IN_MS) > SENSOR_TIMEOUT) {
                timeout_state = TIMED_OUT;
                return 0;
            }
        } 
        else {
            // Timeout not seeing GPIO HIGH from sensor
            uint64_t time_now = sddf_timer_time_now(timer_channel);
            if (((time_now - time_start) / NS_IN_MS) > (SENSOR_TIMEOUT * 100)) {
                timeout_state = TIMED_OUT;
                return 0;
            }

            // Have received measured value before, this is time when value changes
            if (has_received) {
                time_change = sddf_timer_time_now(timer_channel);
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
}

// TODO: might want to buffer over multiple reads
// set trigger pin to LOW then HIGH to fire sensor
void set_trig_low() {
    trig_state = TRIG_LOW;
    digital_write(GPIO_CHANNEL_TRIG, GPIO_LOW);
    timeout_microsec(2);
}

void set_trig_high() {
    trig_state = TRIG_HIGH;
    digital_write(GPIO_CHANNEL_TRIG, GPIO_HIGH);
    timeout_microsec(10);
}

// clean timer states
void reset_states() {
    timeout_state = RUNNING;
    curr_dist = 0;
    trig_state = TRIG_UNSET;
}

// TODO: timeout state
microkit_msginfo send_reading_to_client() {
    microkit_msginfo new_msg = microkit_msginfo_new(0, 1);

    while (true) {
        if (timeout_state == TIMED_OUT) {
            break;
        }
        if (curr_dist != 0) {
            uint64_t distance = curr_dist;
            microkit_mr_set(0, distance);
            break;
        }
    }

    reset_states();
    return new_msg;
}


microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo) {
    switch (ch) {
    case CLIENT_CHANNEL:
        // start up sensor
        set_trig_low();
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

uint64_t read_distance() {
    uint64_t duration = pulse_in(GPIO_CHANNEL_ECHO, GPIO_HIGH);
    if (duration) {
        uint64_t distance = duration * 0.034 / 2;
        LOG_SENSOR("Sensor Reading Received: %ld\n", distance);
        return distance;
    }

    return 0;
}

void notified(sddf_channel ch) {
    // want to send a specific set of signals for sensor to fire
    if (ch == timer_config.driver_id) {
        if (trig_state == TRIG_LOW) {
            set_trig_high();
        }
        else if (trig_state == TRIG_HIGH) {
            curr_dist = read_distance();
        }
    } else {
        LOG_SENSOR("Unexpected channel call\n");
    }
}


void init(void) {
    LOG_SENSOR("Init\n");
    sensor_main();
}

