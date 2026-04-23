

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "include/client/client.h"
#include "include/ultrasonic/ultrasonic_sensor.h"
#include "include/gpio_common/gpio_common.h"

#ifdef DEBUG_LOG
// #define  LOG_SENSOR(...) do{}while(0)
#define LOG_SENSOR(...) do{ sddf_printf("SENSOR|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_SENSOR_ERR(...) do{ sddf_printf("SENSOR|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_SENSOR(...) do{}while(0)
#define LOG_SENSOR_ERR(...) do{}while(0)
#endif


// Read duration of value from GPIO pin (in micro seconds)
uint64_t pulse_in(int gpio_ch, int value)
{
    int measured_value = (value == GPIO_HIGH) ? GPIO_HIGH : GPIO_LOW;
    int delay_value = (value == GPIO_HIGH) ? GPIO_LOW : GPIO_HIGH;

    uint64_t time_start = get_time_now();

    // wait for previous pulse to end -> TOOD check this
    while (digital_read(gpio_ch) == measured_value) {
        uint64_t time_now = get_time_now();
        // TODO check delays
        if (((time_now - time_start) / NS_IN_MS) > SENSOR_TIMEOUT) {
            return 0;
        }
    }

    time_start = get_time_now();

    // wait for pulse to start
    while (digital_read(gpio_ch) == delay_value) {
        uint64_t time_now = get_time_now();
        // TODO check delays
        if (((time_now - time_start) / NS_IN_MS) > SENSOR_TIMEOUT) {
            return 0;
        }
    }

    uint64_t time_received = get_time_now();
    time_start = get_time_now();

    // wait for pulse to stop
    while (digital_read(gpio_ch) == measured_value) {
        uint64_t time_now = get_time_now();
        // TODO check delays
        if (((time_now - time_start) / NS_IN_MS) > SENSOR_TIMEOUT) {
            return 0;
        }
    }

    uint64_t time_stop = get_time_now();
    return (time_stop - time_received) / 1000;
}

void sensor_init(int echo_ch, int trigger_ch)
{
    // TODO: hopefully commeting this out does not break anything
    // sddf_timer_set_timeout(timer_channel, 1*NS_IN_MS);

    LOG_SENSOR("init\n");
    gpio_init(echo_ch, GPIO_DIRECTION_INPUT, SDDF_IRQ_TYPE_NONE);
    gpio_init(trigger_ch, GPIO_DIRECTION_OUTPUT, SDDF_IRQ_TYPE_NONE);
}

// TODO: might want to buffer over multiple reads
// set trigger pin to LOW then HIGH to fire sensor
void set_trig_low(int trigger_ch)
{
    // LOG_SENSOR("Setting trigger low\n");

    digital_write(trigger_ch, GPIO_LOW);
    delay_microseconds(2, SENSOR_TIMEOUT_ID);
}

void set_trig_high(int trigger_ch)
{
    // LOG_SENSOR("Setting trigger high\n");

    digital_write(trigger_ch, GPIO_HIGH);
    delay_microseconds(10, SENSOR_TIMEOUT_ID);
}

uint64_t read_distance(int echo_ch)
{
    uint64_t duration = pulse_in(echo_ch, GPIO_HIGH);
    if (duration) {
        uint64_t distance = duration * 0.034 / 2;
        // LOG_SENSOR("Sensor Reading Received: %ld\n", distance);
        return distance;
    }

    return 0;
}

// TODO: timeout state
// returns distance in cm
uint64_t get_ultrasonic_reading(int echo_ch, int trigger_ch)
{
    // LOG_SENSOR("New loop\n");
    set_trig_low(trigger_ch);
    set_trig_high(trigger_ch);
    return read_distance(echo_ch);
}
