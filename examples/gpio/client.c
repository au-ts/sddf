

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
#define LOG_CLIENT(...) do{ sddf_printf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// cothread_t t_event;
// cothread_t t_main;

// #define STACK_SIZE (4096)
// static char t_client_main_stack[STACK_SIZE];

#define TIMER_CHANNEL (1)

#define GPIO_HIGH (1)
#define GPIO_LOW (0)

// All GPIO 3 pins are for ENA
#define MOTOR_A_GPIO_1 (3)


// Timer States for PWM
#define PAUSE_HIGH (0)
#define PAUSE_LOW (1)

// Motor Controls


#define NS_IN_MS 1000000ULL


// l289n truth table: https://www.dprg.org/l298n-motor-driver-board-drive-modes/
// TODO check if left/right are correct

// https://howtomechatronics.com/tutorials/arduino/arduino-dc-motor-control-tutorial-l298n-pwm-h-bridge/#:~:text=Next%20are%20the%20logic%20control,the%20motor%20will%20be%20disabled.

int pwm_state = PAUSE_LOW;
int curr_control = ;

void gpio_init(int gpio_ch) {
    // LOG_CLIENT("Setting direction of GPIO1 to output!\n");
    microkit_msginfo msginfo;
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_DIRECTION);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, GPIO_DIRECTION_OUTPUT);
    msginfo = microkit_ppcall(gpio_ch, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set direction of gpio with error %ld!\n", error);
        while (1) {};
    }
}

// GPIO output HIGH/LOW
void digital_write(int gpio_ch, int value) {
    microkit_msginfo msginfo;

    if (value == GPIO_HIGH) {
        // LOG_CLIENT("Setting GPIO1 to on!\n");
        msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
        microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
        microkit_mr_set(GPIO_REQ_VALUE_SLOT, 1);
        msginfo = microkit_ppcall(gpio_ch, msginfo);
        if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
            size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
            LOG_CLIENT_ERR("failed to set output of gpio with error %ld!\n", error);
            while (1) {};
        }       
    }
    else if (value == GPIO_LOW) {
        // TODO check if this is correct to set GPIO LOW
        // LOG_CLIENT("Setting GPIO1 to off!\n");
        msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
        microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
        microkit_mr_set(GPIO_REQ_VALUE_SLOT, 0);
        msginfo = microkit_ppcall(gpio_ch, msginfo);
        if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
            size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
            // LOG_CLIENT_ERR("failed to set output of gpio with error %ld!\n", error);
            while (1) {};
        }
    }
}

void set_pwm(int gpio_ch, int micro_s) {
    // LOG_CLIENT("SET DIGITAL HIGH\n");
    digital_write(gpio_ch, GPIO_HIGH);
    pwm_state = PAUSE_HIGH;

    // timeout to drive motor forward
    sddf_timer_set_timeout(TIMER_CHANNEL, micro_s);
}

void control_loop_main(void) {
    gpio_init(MOTOR_A_GPIO_1);

    // hold high for 2 ms
    set_pwm(MOTOR_A_GPIO_1, 2*NS_IN_MS);
    digital_write(MOTOR_A_GPIO_1, GPIO_HIGH);

}

void notified(microkit_channel ch) {
    // check this switch
    switch (ch)
    {
    case TIMER_CHANNEL:
        // LOG_CLIENT("PWM TIMEOUT\n");
        if (pwm_state == PAUSE_HIGH) {
            digital_write(MOTOR_A_GPIO_1, GPIO_LOW);
            uint64_t time = sddf_timer_time_now(TIMER_CHANNEL);
            LOG_CLIENT("SET DIGITAL LOW, the time now is: %lu\n", time);
            
            // hold low for 18 ms
            sddf_timer_set_timeout(TIMER_CHANNEL, 18*NS_IN_MS);
            pwm_state = PAUSE_LOW;
        }
        else {
            uint64_t time = sddf_timer_time_now(TIMER_CHANNEL);
            LOG_CLIENT("SET DIGITAL HIGH, the time now is: %lu\n", time);

            set_pwm(MOTOR_A_GPIO_1, 2*NS_IN_MS);
        }   
       
        break;
    default:
        LOG_CLIENT("Unexpected channel call\n");
        break;
    }
}

void init(void) {
    LOG_CLIENT("Init\n");
    control_loop_main();
}

