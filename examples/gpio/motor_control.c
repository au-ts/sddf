

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "include/motor/motor_control.h"
#include "include/client/client.h"
#include "include/gpio_common/gpio_common.h"

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
// #define  LOG_CONTROL(...) do{}while(0)
#define LOG_CONTROL(...) do{ sddf_printf("CONTROL|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define  LOG_CONTROL(...) do{}while(0)
#endif

#define LOG_CONTROL_ERR(...) do{ sddf_printf("CONTROL|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)


// Channels

// Motors A and B channels
#define GPIO_CHANNEL_A (5)
#define GPIO_CHANNEL_B (6)

// Timer States for PWM
#define PAUSE_HIGH (0)
#define PAUSE_LOW (1)


// Motor/PWM States

int pwm_a_state = PAUSE_LOW;
int pwm_b_state = PAUSE_LOW;

int motor_a_state = CONTROL_NEUTRAL;
int motor_b_state = CONTROL_NEUTRAL;

// State of Current Control
uint64_t request_time_end = 0;
int is_control_fulfilled = 0;

void set_pwm(int gpio_ch, uint64_t micro_s) {
    digital_write(gpio_ch, GPIO_HIGH);
    size_t time_ns = micro_s * NS_IN_US;

    // TODO: refactor this
    if (gpio_ch == GPIO_CHANNEL_A) {
        pwm_a_state = PAUSE_HIGH;
    }
    else if (gpio_ch == GPIO_CHANNEL_B) {
        pwm_b_state = PAUSE_HIGH;
    }

    enqueue(&timeout_queue, get_time_now() + time_ns, gpio_ch);
    // timeout to drive motor forward
    set_timeout(micro_s);
}

void control_forward(void) {
    is_control_fulfilled = 1;

    motor_a_state = CONTROL_FORWARD;
    motor_b_state = CONTROL_FORWARD;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]);
}

// TODO complete these
void control_reverse(void) {
    is_control_fulfilled = 1;

    motor_a_state = CONTROL_REVERSE;
    motor_b_state = CONTROL_REVERSE;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_REVERSE - 1][PWM_TIME_HIGH]);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_REVERSE - 1][PWM_TIME_HIGH]);
}


void control_neutral(void) {
    is_control_fulfilled = 1;

    motor_a_state = CONTROL_NEUTRAL;
    motor_b_state = CONTROL_NEUTRAL;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]);
}

void control_left(void) {
    is_control_fulfilled = 1;

    motor_a_state = CONTROL_NEUTRAL;
    motor_b_state = CONTROL_FORWARD;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]);
}

void control_right(void) {
    is_control_fulfilled = 1;

    motor_a_state = CONTROL_FORWARD;
    motor_b_state = CONTROL_NEUTRAL;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]);
}

// void handle_motor_request(int control_request) {
//     is_control_fulfilled = 1;

//     switch (control_request)
//     {
//     case REQUEST_FORWARD:
//         set_forward();
//         break;
//     case REQUEST_BACK:
//         set_reverse();
//         break;
//     case REQUEST_LEFT:
//         set_left();
//         break;
//     case REQUEST_RIGHT:
//         set_right();
//         break;
//     case REQUEST_NEUTRAL:
//         set_neutral();
//         break;
//     default:
//         break;
//     }
// }

// microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo) {
//     switch (ch) {
//     case CLIENT_CHANNEL:
//         int request = (int) microkit_mr_get(0);
//         int was_control_fulfilled = is_control_fulfilled;

//         uint64_t request_duration = microkit_mr_get(1);
//         request_time_end = sddf_timer_time_now(timer_channel) + request_duration;

//         if (!request) {
//             break;
//         }

//         control_request = request;
//         is_control_fulfilled = 0;

//         // first control request, call a function to handle it
//         if (was_control_fulfilled < 0) {
//             // TODO: is this correct?
//             handle_motor_request();
//         }
        
//         // block while current time < request duration
//         // TODO: might want to use delay_ms here, check if it faults & if timer interrupts will be handled appropriately
//         while (sddf_timer_time_now(timer_channel) < request_time_end){}
//         break;
//     default:
//         LOG_CONTROL("Unexpected pp call\n");
//         break;
//     }

//     microkit_msginfo res = microkit_msginfo_new(0, 0);
//     return res;
// } 

// handle current motor command timeout, update control states
void handle_motor_control_timeout() {
    is_control_fulfilled = 0;
    control_neutral();
}

// upon pwm timeout, send next gpio signal
void handle_pwm_timeout(int gpio_ch) {
    // if (!is_control_fulfilled) {
    //     handle_motor_request();
    //     return;
    // }

    // LOG_CONTROL("handling pwm timeout %d\n", gpio_ch);

    // TODO: refactor this
    if (gpio_ch == GPIO_CHANNEL_A) {
        // LOG_CONTROL("handling motor A pwm\n");
        if (pwm_a_state == PAUSE_HIGH) {
            digital_write(gpio_ch, GPIO_LOW);
            size_t time_ns = pwm_delay_mappings[motor_a_state - 1][PWM_TIME_LOW]*NS_IN_US;

            enqueue(&timeout_queue, get_time_now() + time_ns, gpio_ch);
            set_timeout(pwm_delay_mappings[motor_a_state - 1][PWM_TIME_LOW]);
            pwm_a_state = PAUSE_LOW;
        }
        else {
            set_pwm(gpio_ch, pwm_delay_mappings[motor_a_state - 1][PWM_TIME_HIGH]);
        }
    }
    else if (gpio_ch == GPIO_CHANNEL_B) {
        if (pwm_b_state == PAUSE_HIGH) {
            digital_write(gpio_ch, GPIO_LOW);
            size_t time_ns = pwm_delay_mappings[motor_b_state - 1][PWM_TIME_LOW]*NS_IN_US;

            enqueue(&timeout_queue, get_time_now() + time_ns, gpio_ch);
            set_timeout(pwm_delay_mappings[motor_b_state - 1][PWM_TIME_LOW]);
            pwm_b_state = PAUSE_LOW;
        }
        else {
            set_pwm(gpio_ch, pwm_delay_mappings[motor_b_state - 1][PWM_TIME_HIGH]);
        }
    }
}


// void notified(sddf_channel ch) {
//     if (ch == timer_config.driver_id) {
//         if (sddf_timer_time_now(timer_channel) >= request_time_end) {
//             return;
//         }
//         int motor_channel = dequeue(&timeout_queue);
//         handle_pwm_timeout(motor_channel);
//     }
//     else {
//         LOG_CONTROL("Unexpected channel call\n");
//     }
// }


void motors_init(void) {
    is_control_fulfilled = 0;

    LOG_CONTROL("Init\n");
    gpio_init(GPIO_CHANNEL_A, GPIO_DIRECTION_OUTPUT);
    gpio_init(GPIO_CHANNEL_B, GPIO_DIRECTION_OUTPUT);
}

