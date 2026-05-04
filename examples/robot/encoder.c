

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "include/motor/encoder.h"

#define DEBUG_LOG

#ifdef DEBUG_LOG
#define LOG_ENCODER(...) do{ sddf_printf("ENCODER|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_ENCODER_ERR(...) do{ sddf_printf("ENCODER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_ENCODER(...) do{}while(0)
#define LOG_ENCODER_ERR(...) do{}while(0)
#endif

int encoder_count = 0;

// polling approach since driver IRQs might be cooked
// TODO: update this with an IRQ later
// code: https://forum.arduino.cc/t/controlling-motor-speed-in-rpm-using-an-encoder/1276093/5
void detect_encoder_rising_edge(int gpio_ch_a, int gpio_ch_b) {
    int prev_a_state = GPIO_LOW; 
    int prev_b_state = GPIO_LOW;

    int curr_a_state = digital_read(gpio_ch_a);
    int curr_b_state = digital_read(gpio_ch_b);

    while (true) {
        if (prev_a_state == GPIO_LOW && curr_a_state == GPIO_HIGH) {
            prev_a_state = GPIO_HIGH;

            if (curr_b_state) {
                encoder_count++;
            }
            else {
                encoder_count--;
            }
        } else if (prev_b_state == GPIO_LOW && curr_b_state == GPIO_HIGH) {
            prev_b_state = GPIO_HIGH;

            if (curr_a_state) {
                encoder_count++;
            }
            else {
                encoder_count--;
            }
        }

        if (curr_a_state == GPIO_LOW) {
            prev_a_state = GPIO_LOW;
        }
        if (curr_b_state == GPIO_LOW) {
            prev_b_state = GPIO_LOW;
        }
    }
}


void encoder_init(int gpio_ch_a, int gpio_ch_b)
{
    LOG_ENCODER("init\n");
    gpio_init(gpio_ch_a, GPIO_DIRECTION_INPUT, SDDF_IRQ_TYPE_NONE);
    gpio_init(gpio_ch_b, GPIO_DIRECTION_INPUT, SDDF_IRQ_TYPE_NONE);
}
