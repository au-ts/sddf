

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "include/client/client.h"
#include "include/ultrasonic/ultrasonic_sensor.h"
#include "include/gpio_common/gpio_common.h"

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
// #define  LOG_SENSOR(...) do{}while(0)
#define LOG_SENSOR(...) do{ sddf_printf("SENSOR|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define  LOG_SENSOR(...) do{}while(0)
#endif

#define LOG_SENSOR_ERR(...) do{ sddf_printf("SENSOR|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// Read duration of value from GPIO pin (in micro seconds)
uint64_t pulse_in(int gpio_ch, int value) {
    uint64_t time_start = get_time_now();
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
                time_received = get_time_now();
                continue;
            }

            uint64_t time_now = get_time_now();

            if (((time_now - time_start) / NS_IN_MS) > SENSOR_TIMEOUT) {
                LOG_SENSOR("timeout 1\n");
                return 0;
            }
        } 
        else {
            // Timeout not seeing GPIO HIGH from sensor
            uint64_t time_now = get_time_now();
            if (((time_now - time_start) / NS_IN_MS) > (SENSOR_TIMEOUT * 100)) {
                LOG_SENSOR("timeout 2\n");
                return 0;
            }

            // Have received measured value before, this is time when value changes
            if (has_received) {
                time_change = get_time_now();
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

void sensor_init(void) {
    // TODO: hopefully commeting this out does not break anything
    // sddf_timer_set_timeout(timer_channel, 1*NS_IN_MS);

    LOG_SENSOR("init\n");
    gpio_init(GPIO_CHANNEL_ECHO, GPIO_DIRECTION_INPUT);
    gpio_init(GPIO_CHANNEL_TRIG, GPIO_DIRECTION_OUTPUT);  
}

// TODO: might want to buffer over multiple reads
// set trigger pin to LOW then HIGH to fire sensor
void set_trig_low() {
    LOG_SENSOR("Setting trigger low\n");

    digital_write(GPIO_CHANNEL_TRIG, GPIO_LOW);
        // enqueue(&timeout_queue, sddf_timer_time_now(timer_channel) + micro_s, gpio_ch);

    delay_microseconds(2, SENSOR_TIMEOUT_ID);
}

void set_trig_high() {
    LOG_SENSOR("Setting trigger high\n");

    digital_write(GPIO_CHANNEL_TRIG, GPIO_HIGH);
    delay_microseconds(10, SENSOR_TIMEOUT_ID);
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

// TODO: timeout state
// returns distance in cm
uint64_t get_ultrasonic_reading() {
    set_trig_low();
    set_trig_high();
    return read_distance();
}

