

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
#include "client.h"
#include "gpio_config.h"

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CONTROL(...) do{ sddf_printf("CONTROL|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define  LOG_CONTROL(...) do{}while(0)
#endif

#define LOG_CONTROL_ERR(...) do{ sddf_printf("CONTROL|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

uintptr_t control_buffer_base_vaddr;

// Channels
#define CLIENT_CHANNEL (1)
#define TIMER_CHANNEL (2)
#define GPIO_CHANNEL (3)

#define GPIO_HIGH (1)
#define GPIO_LOW (0)

// Timer States for PWM
#define PAUSE_HIGH (0)
#define PAUSE_LOW (1)

int pwm_state = PAUSE_LOW;
int curr_command = CONTROL_NEUTRAL;

// State of Current Control
int is_control_fulfilled = -1;

// Read data sent from client in the control buffer
int read_control_buffer() {
    int ch = 0;

    if ((*REG_PTR(control_buffer_base_vaddr, UARTFR) & PL011_UARTFR_RXFE) == 0) {
        ch = *REG_PTR(control_buffer_base_vaddr, UARTDR) & RHR_MASK;
    }

    return ch;
}


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
    // LOG_CONTROL("SET DIGITAL HIGH\n");
    digital_write(gpio_ch, GPIO_HIGH);
    pwm_state = PAUSE_HIGH;

    // timeout to drive motor forward
    sddf_timer_set_timeout(TIMER_CHANNEL, micro_s);
}


void set_forward(void) {
    set_pwm(GPIO_CHANNEL, pwm_delay_mappings[CONTROL_FORWARD - 1][PWM_TIME_HIGH]*NS_IN_US);
}

// TODO complete these
void set_reverse(void) {
    set_pwm(GPIO_CHANNEL, pwm_delay_mappings[CONTROL_REVERSE - 1][PWM_TIME_HIGH]*NS_IN_US);
}

void set_neutral(void) {
    set_pwm(GPIO_CHANNEL, pwm_delay_mappings[CONTROL_NEUTRAL - 1][PWM_TIME_HIGH]*NS_IN_US);
}


void handle_motor_request(void) {
    switch (curr_command)
    {
    case CONTROL_FORWARD:
        set_forward();
        break;
    case CONTROL_REVERSE:
        set_reverse();
        break;
    case CONTROL_NEUTRAL:
        set_neutral();
        break;
    default:
        break;
    }
}

void notified(microkit_channel ch) {
    switch (ch)
    {
    case TIMER_CHANNEL:
        // new control request, stop current signal to make new one
        if (!is_control_fulfilled) {
            handle_motor_request();
            is_control_fulfilled = 1;
            break;
        } 

        if (pwm_state == PAUSE_HIGH) {
            digital_write(GPIO_CHANNEL, GPIO_LOW);
            // uint64_t time = sddf_timer_time_now(TIMER_CHANNEL);
            // LOG_CONTROL("SET DIGITAL LOW, the time now is: %lu\n", time);
            LOG_CONTROL("CURRENT CONTROL, %d\n", curr_command);
            
            // TODO change this to corresponding down time for each motor direction
            // hold low for 18 ms (to drive forward)
            sddf_timer_set_timeout(TIMER_CHANNEL, pwm_delay_mappings[curr_command - 1][PWM_TIME_LOW]*NS_IN_US);
            pwm_state = PAUSE_LOW;
        }
        else {
            // uint64_t time = sddf_timer_time_now(TIMER_CHANNEL);
            // LOG_CONTROL("SET DIGITAL HIGH, the time now is: %lu\n", time);
            set_pwm(GPIO_CHANNEL, pwm_delay_mappings[curr_command - 1][PWM_TIME_HIGH]*NS_IN_US);
        }   
        
        break;
    case CLIENT_CHANNEL:
        int command = read_control_buffer();
        int was_control_fulfilled = is_control_fulfilled;

        if (!command) {
            break;
        }
        curr_command = command;
        is_control_fulfilled = 0;

        // first control request, call a function to handle it
        if (was_control_fulfilled < 0) {
            handle_motor_request();
        }

        break;
    default:
        LOG_CONTROL("Unexpected channel call\n");
        break;
    }
}

void init(void) {
    LOG_CONTROL("Init\n");
    gpio_init(GPIO_CHANNEL);
}

