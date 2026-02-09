

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
// #define GPIO_CHANNEL_A (5)
// #define GPIO_CHANNEL_B (6)

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
    if (gpio_ch == gpio_channel_motor_a) {
        pwm_a_state = PAUSE_HIGH;
    }
    else if (gpio_ch == gpio_channel_motor_b) {
        pwm_b_state = PAUSE_HIGH;
    }

    enqueue(&timeout_queue, get_time_now() + time_ns, gpio_ch);
    set_timeout(micro_s);
}

void control_forward(uint64_t miliseconds) {
    delay_miliseconds(miliseconds, MOTOR_CONTROL_TIMEOUT_ID);

    is_control_fulfilled = 1;

    motor_a_state = CONTROL_FORWARD;
    motor_b_state = CONTROL_FORWARD;

    set_pwm(gpio_channel_motor_a, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]);
    set_pwm(gpio_channel_motor_b, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]);
}

// TODO complete these
void control_reverse(uint64_t miliseconds) {
    delay_miliseconds(miliseconds, MOTOR_CONTROL_TIMEOUT_ID);

    is_control_fulfilled = 1;

    motor_a_state = CONTROL_REVERSE;
    motor_b_state = CONTROL_REVERSE;

    set_pwm(gpio_channel_motor_a, pwm_delay_mappings[CONTROL_REVERSE - 1][PWM_TIME_HIGH]);
    set_pwm(gpio_channel_motor_b, pwm_delay_mappings[CONTROL_REVERSE - 1][PWM_TIME_HIGH]);
}


void control_neutral(uint64_t miliseconds) {
    delay_miliseconds(miliseconds, MOTOR_CONTROL_TIMEOUT_ID);

    is_control_fulfilled = 1;

    motor_a_state = CONTROL_NEUTRAL;
    motor_b_state = CONTROL_NEUTRAL;

    set_pwm(gpio_channel_motor_a, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]);
    set_pwm(gpio_channel_motor_b, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]);
}

void control_left(uint64_t miliseconds) {
    delay_miliseconds(miliseconds, MOTOR_CONTROL_TIMEOUT_ID);

    is_control_fulfilled = 1;

    motor_a_state = CONTROL_NEUTRAL;
    motor_b_state = CONTROL_FORWARD;

    set_pwm(gpio_channel_motor_a, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]);
    set_pwm(gpio_channel_motor_b, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]);
}

void control_right(uint64_t miliseconds) {
    delay_miliseconds(miliseconds, MOTOR_CONTROL_TIMEOUT_ID);

    is_control_fulfilled = 1;

    motor_a_state = CONTROL_FORWARD;
    motor_b_state = CONTROL_NEUTRAL;

    set_pwm(gpio_channel_motor_a, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]);
    set_pwm(gpio_channel_motor_b, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]);
}

void control_stop() {
    digital_write(gpio_channel_motor_a, GPIO_LOW);
    digital_write(gpio_channel_motor_b, GPIO_LOW);
}

// handle current motor command timeout, update control states
void handle_motor_control_timeout() {
    is_control_fulfilled = 0;
    
    // Stop motors immediately
    control_stop();

    // Reset PWM states so any queued timeouts won't restart PWM
    pwm_a_state = PAUSE_LOW;
    pwm_b_state = PAUSE_LOW;
}

// upon pwm timeout, send next gpio signal
void handle_pwm_timeout(int gpio_ch) {
    // new request coming in
    if (!is_control_fulfilled) {
        LOG_CONTROL("control timeout\n");
        control_stop();
        return;
    }

    // TODO: refactor this
    if (gpio_ch == gpio_channel_motor_a) {
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
    else if (gpio_ch == gpio_channel_motor_b) {
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

void motors_init(void) {
    is_control_fulfilled = 0;

    LOG_CONTROL("Init\n");
    gpio_init(gpio_channel_motor_a, GPIO_DIRECTION_OUTPUT);
    gpio_init(gpio_channel_motor_b, GPIO_DIRECTION_OUTPUT);
}

