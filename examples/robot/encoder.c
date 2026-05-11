

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "include/motor/encoder.h"

// #define DEBUG_LOG

#ifdef DEBUG_LOG
#define LOG_ENCODER(...) do{ sddf_printf("ENCODER|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_ENCODER_ERR(...) do{ sddf_printf("ENCODER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_ENCODER(...) do{}while(0)
#define LOG_ENCODER_ERR(...) do{}while(0)
#endif

int encoder_count = 0;

// void detect_encoder_rising_edge(int gpio_ch_a, int gpio_ch_b) {
//     int prev_a_state = GPIO_LOW; 
//     int prev_b_state = GPIO_LOW;

//     while (true) {
//         if (prev_a_state == GPIO_LOW && digital_read(gpio_ch_a) == GPIO_HIGH) {
//             prev_a_state = GPIO_HIGH;
//             LOG_ENCODER("rising edge in A\n");
//         } 
//         else if (digital_read(gpio_ch_b) == GPIO_LOW) {
//             prev_a_state = GPIO_LOW;
//         }

//         if (prev_b_state == GPIO_LOW && digital_read(gpio_ch_b) == GPIO_HIGH) {
//             prev_b_state = GPIO_HIGH;
//             LOG_ENCODER("rising edge in B\n");
//         }
//         else if (digital_read(gpio_ch_b) == GPIO_LOW) {
//             prev_b_state = GPIO_LOW;
//         }
//     }
// }

// Quadrature encoder polling using state transitions
// Detects rising edges on each pin and checks the other pin to determine direction
void detect_encoder_rising_edge(int gpio_ch_a, int gpio_ch_b, int timer_channel) {
    int prev_a_state = GPIO_LOW; 
    int prev_b_state = GPIO_LOW;

    uint64_t prev_time = sddf_timer_time_now(timer_channel);

    while (true) {
        uint64_t curr_time = sddf_timer_time_now(timer_channel);

        if (curr_time - prev_time >= NS_IN_S) {
            // calculate revolutions per second
            double wheel_ppr = PPR * REDUCTION;
            double rpm = (encoder_count / wheel_ppr)*60;
            // TOOD: should this be reset here?
            prev_time = curr_time;

            LOG_ENCODER("Encoder: %f\n", rpm);
        }

        int curr_a_state = digital_read(gpio_ch_a);
        int curr_b_state = digital_read(gpio_ch_b);

        // detect rising edge on pin A
        if (prev_a_state == GPIO_LOW && curr_a_state == GPIO_HIGH) {
            // check Pin B for direction
            if (curr_b_state == GPIO_LOW) {
                encoder_count++;
                LOG_ENCODER("A rising, B low\n");
            } else {
                encoder_count--;
                LOG_ENCODER("A rising, B high\n");
            }
        }

        // detect rising edge on pin B
        if (prev_b_state == GPIO_LOW && curr_b_state == GPIO_HIGH) {
            // check Pin A for direction
            if (curr_a_state == GPIO_LOW) {
                encoder_count--;
                LOG_ENCODER("B rising, A low\n");
            } else {
                encoder_count++;
                LOG_ENCODER("B rising, A high\n");
            }
        }

        prev_a_state = curr_a_state;
        prev_b_state = curr_b_state;
    }
}


void encoder_init(int gpio_ch_a, int gpio_ch_b)
{
    LOG_ENCODER("init\n");
    gpio_init(gpio_ch_a, GPIO_DIRECTION_INPUT, SDDF_IRQ_TYPE_NONE);
    gpio_init(gpio_ch_b, GPIO_DIRECTION_INPUT, SDDF_IRQ_TYPE_NONE);
}
