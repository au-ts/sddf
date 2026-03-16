

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

#define CH_PWM_CONTROL_PPC 0

// Motors A and B channels
/* We use PWM2 (channel 1) which is connected to IO_GPIO13 by our pinctrl driver */
#define PWM_CHANNEL_MOTOR_A 1

/* We use PWM4 (channel 3) which is connected to IO_GPIO15 by our pinctrl driver */
#define PWM_CHANNEL_MOTOR_B 3

int motor_a_state = CONTROL_NEUTRAL;
int motor_b_state = CONTROL_NEUTRAL;

// takes pulse width (microseconds), period (microseconds)
void set_pwm(int pwm_ch, uint64_t pulse_width, uint64_t period) {
    bool success;
    success = sddf_pwm_set_ns(CH_PWM_CONTROL_PPC, pwm_ch, period*NS_IN_US, pulse_width*NS_IN_US, /* flags */ 0);

    assert(success);
}

void control_forward() {
    motor_a_state = CONTROL_FORWARD;
    motor_b_state = CONTROL_FORWARD;

    set_pwm(PWM_CHANNEL_MOTOR_A, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
    set_pwm(PWM_CHANNEL_MOTOR_B, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
}

void control_reverse() {
    motor_a_state = CONTROL_REVERSE;
    motor_b_state = CONTROL_REVERSE;

    set_pwm(PWM_CHANNEL_MOTOR_A, pwm_delay_mappings[CONTROL_REVERSE - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
    set_pwm(PWM_CHANNEL_MOTOR_B, pwm_delay_mappings[CONTROL_REVERSE - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
}

void control_neutral() {
    motor_a_state = CONTROL_NEUTRAL;
    motor_b_state = CONTROL_NEUTRAL;

    set_pwm(PWM_CHANNEL_MOTOR_A, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
    set_pwm(PWM_CHANNEL_MOTOR_B, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
}

void control_left() {
    motor_a_state = CONTROL_NEUTRAL;
    motor_b_state = CONTROL_FORWARD;

    set_pwm(PWM_CHANNEL_MOTOR_A, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
    set_pwm(PWM_CHANNEL_MOTOR_B, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
}

void control_right() {
    motor_a_state = CONTROL_FORWARD;
    motor_b_state = CONTROL_NEUTRAL;

    set_pwm(PWM_CHANNEL_MOTOR_A, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
    set_pwm(PWM_CHANNEL_MOTOR_B, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH], PWM_MOTOR_PERIOD);
}

void control_stop() {
    /* disable PWM */
    set_pwm(PWM_CHANNEL_MOTOR_A, 0, 0);
    set_pwm(PWM_CHANNEL_MOTOR_B, 0, 0);
}
