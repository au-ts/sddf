

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
#include "include/motor/motor_control.h"
#include "include/motor/timer_queue.h"
#include "gpio_config.h"

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define  LOG_CONTROL(...) do{}while(0)
// #define LOG_CONTROL(...) do{ sddf_printf("CONTROL|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define  LOG_CONTROL(...) do{}while(0)
#endif

#define LOG_CONTROL_ERR(...) do{ sddf_printf("CONTROL|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

sddf_channel timer_channel;

// uintptr_t control_buffer_base_vaddr;

// Channels
#define CLIENT_CHANNEL (1)

// Motors A and B channels
#define GPIO_CHANNEL_A (2)
#define GPIO_CHANNEL_B (3)

#define GPIO_HIGH (1)
#define GPIO_LOW (0)

// Timer States for PWM
#define PAUSE_HIGH (0)
#define PAUSE_LOW (1)

PriorityQueue timeout_queue = {{}, {}, 0};

// Motor/PWM States
int pwm_a_state = PAUSE_LOW;
int pwm_b_state = PAUSE_LOW;

int motor_a_state = CONTROL_STOP;
int motor_b_state = CONTROL_STOP;

int control_request = REQUEST_STOP;

// State of Current Control
int is_control_fulfilled = -1;

void gpio_init(int gpio_ch) {
    // LOG_CONTROL("Setting direction of GPIO1 to output!\n");
    microkit_msginfo msginfo;
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_DIRECTION);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, GPIO_DIRECTION_OUTPUT);
    msginfo = microkit_ppcall(gpio_ch, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CONTROL_ERR("failed to set direction of gpio with error %ld!\n", error);
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
            LOG_CONTROL_ERR("failed to set output of gpio with error %ld!\n", error);
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
            LOG_CONTROL_ERR("failed to set output of gpio with error %ld!\n", error);
            while (1) {};
        }
    }
}

void set_pwm(int gpio_ch, int micro_s) {
    digital_write(gpio_ch, GPIO_HIGH);

    // TODO: refactor this
    if (gpio_ch == GPIO_CHANNEL_A) {
        pwm_a_state = PAUSE_HIGH;
    }
    else if (gpio_ch == GPIO_CHANNEL_B) {
        pwm_b_state = PAUSE_HIGH;
    }

    enqueue(&timeout_queue, sddf_timer_time_now(), gpio_ch);
    // timeout to drive motor forward
    sddf_timer_set_timeout(timer_channel, micro_s);
}

void set_forward(void) {
    motor_a_state = CONTROL_FORWARD;
    motor_b_state = CONTROL_FORWARD;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]*NS_IN_US);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]*NS_IN_US);
}

// TODO complete these
void set_reverse(void) {
    motor_a_state = CONTROL_REVERSE;
    motor_b_state = CONTROL_REVERSE;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_REVERSE - 1][PWM_TIME_HIGH]*NS_IN_US);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_REVERSE - 1][PWM_TIME_HIGH]*NS_IN_US);
}

void set_neutral(void) {
    motor_a_state = CONTROL_NEUTRAL;
    motor_b_state = CONTROL_NEUTRAL;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]*NS_IN_US);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]*NS_IN_US);
}

void set_left(void) {
    motor_a_state = CONTROL_NEUTRAL;
    motor_b_state = CONTROL_FORWARD;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]*NS_IN_US);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]*NS_IN_US);
}

void set_right(void) {
    motor_a_state = CONTROL_FORWARD;
    motor_b_state = CONTROL_NEUTRAL;

    set_pwm(GPIO_CHANNEL_A, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]*NS_IN_US);
    set_pwm(GPIO_CHANNEL_B, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]*NS_IN_US);
}

void handle_motor_request(void) {
    is_control_fulfilled = 1;

    switch (control_request)
    {
    case REQUEST_FORWARD:
        set_forward();
        break;
    case REQUEST_BACK:
        set_reverse();
        break;
    case REQUEST_LEFT:
        set_left();
        break;
    case REQUEST_RIGHT:
        set_right();
        break;
    case REQUEST_NEUTRAL:
        set_neutral();
        break;
    case REQUEST_STOP:
        set_stop();
        break;
    default:
        break;
    }
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo) {
    switch (ch) {
    case CLIENT_CHANNEL:
        int request = (int) microkit_mr_get(0);
        int was_control_fulfilled = is_control_fulfilled;

        if (!request) {
            break;
        }

        control_request = request;
        is_control_fulfilled = 0;

        // first control request, call a function to handle it
        if (was_control_fulfilled < 0) {
            // TODO: is this correct?
            handle_motor_request();
        }
        break;
    default:
        LOG_CONTROL("Unexpected pp call\n");
        break;
    }

    microkit_msginfo res = microkit_msginfo_new(0, 0);
    return res;
} 

// upon pwm timeout, send next gpio signal
void handle_pwm_timeout(int gpio_ch) {
    if (!is_control_fulfilled) {
        handle_motor_request();
        return;
    }

    // TODO: refactor this
    if (gpio_ch == GPIO_CHANNEL_A) {
        if (pwm_a_state == PAUSE_HIGH) {
            digital_write(gpio_ch, GPIO_LOW);
            sddf_timer_set_timeout(timer_channel, pwm_delay_mappings[motor_a_state - 1][PWM_TIME_LOW]*NS_IN_US);
            pwm_a_state = PAUSE_LOW;
        }
        else {
            set_pwm(gpio_ch, pwm_delay_mappings[motor_a_state - 1][PWM_TIME_HIGH]*NS_IN_US);
        }
    }
    else if (gpio_ch == GPIO_CHANNEL_B) {
        if (pwm_b_state == PAUSE_HIGH) {
            digital_write(gpio_ch, GPIO_LOW);
            sddf_timer_set_timeout(timer_channel, pwm_delay_mappings[motor_b_state - 1][PWM_TIME_LOW]*NS_IN_US);
            pwm_b_state = PAUSE_LOW;
        }
        else {
            set_pwm(gpio_ch, pwm_delay_mappings[motor_b_state - 1][PWM_TIME_HIGH]*NS_IN_US);
        }
    }
}


void notified(sddf_channel ch) {
    if (ch == timer_config.driver_id) {
        int motor_channel = dequeue(&timeout_queue);
        handle_pwm_timeout(motor_channel);
    }
    else {
        LOG_CONTROL("Unexpected channel call\n");
    }
}

void init(void) {
    timer_channel = timer_config.driver_id;

    LOG_CONTROL("Init\n");
    gpio_init(GPIO_CHANNEL_A);
    gpio_init(GPIO_CHANNEL_B);
}

