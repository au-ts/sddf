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
#define LOG_CLIENT(...) do{ sddf_dprintf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
#define GPIO_HIGH (1);
#define GPIO_LOW (0);


// All GPIO 3 pins are for ENA
#define MOTOR_A_GPIO_1 (0);
#define MOTOR_A_GPIO_2 (1);
#define MOTOR_A_GPIO_3 (2);

#define MOTOR_B_GPIO_1 (3);
#define MOTOR_B_GPIO_2 (4);
#define MOTOR_B_GPIO_3 (5);


static char t_client_main_stack[STACK_SIZE];

// GPIO output HIGH/LOW
void digital_write(int gpio_ch, int value) {
    LOG_CLIENT("Setting direction of GPIO1 to output!\n");
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_DIRECTION);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, GPIO_DIRECTION_OUTPUT);
    msginfo = microkit_ppcall(gpio_ch, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set direction of gpio with error %ld!\n", error);
        while (1) {};
    }

    if (value == GPIO_HIGH) {
        LOG_CLIENT("Setting GPIO1 to on!\n");
        msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
        microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
        microkit_mr_set(GPIO_REQ_VALUE_SLOT, 0);
        msginfo = microkit_ppcall(gpio_ch, msginfo);
        if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
            size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
            LOG_CLIENT_ERR("failed to set output of gpio with error %ld!\n", error);
            while (1) {};
        }

        // TODO check what drive strength is good to drive motor
        LOG_CLIENT("Setting GPIO1 drive strength to 4000UA!\n");
        msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
        microkit_mr_set(GPIO_REQ_CONFIG_SLOT, MESON_GPIO_DRIVE_STRENGTH);
        microkit_mr_set(GPIO_REQ_VALUE_SLOT, MESON_GPIO_DS_4000UA);
        msginfo = microkit_ppcall(gpio_ch, msginfo);
        if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
            size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
            LOG_CLIENT_ERR("failed to set output of gpio with error %ld!\n", error);
            while (1) {};
        }        
    }
    else if (value == GPIO_LOW) {
        // TODO check if this is correct to set GPIO LOW
        LOG_CLIENT("Setting GPIO1 to off!\n");
        msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
        microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
        microkit_mr_set(GPIO_REQ_VALUE_SLOT, 0);
        msginfo = microkit_ppcall(gpio_ch, msginfo);
        if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
            size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
            LOG_CLIENT_ERR("failed to set output of gpio with error %ld!\n", error);
            while (1) {};
        }
    }
}

// l289n truth table: https://www.dprg.org/l298n-motor-driver-board-drive-modes/
// TODO check if left/right are correct
void control_left() {
    // Set motor 2 forward
    digital_write(MOTOR_B_GPIO_1, GPIO_LOW);
    digital_write(MOTOR_B_GPIO_2, GPIO_HIGH);
    digital_write(MOTOR_B_GPIO_3, GPIO_HIGH);

    // Set motor 1 to coast
    digital_write(MOTOR_A_GPIO_1, GPIO_LOW);
    digital_write(MOTOR_A_GPIO_2, GPIO_HIGH);
    digital_write(MOTOR_A_GPIO_3, GPIO_LOW);
}

void control_right() {
    // Set motor 1 forward
    digital_write(MOTOR_A_GPIO_1, GPIO_LOW);
    digital_write(MOTOR_A_GPIO_2, GPIO_HIGH);
    digital_write(MOTOR_A_GPIO_3, GPIO_HIGH);

    // Set motor 2 coast
    digital_write(MOTOR_B_GPIO_1, GPIO_LOW);
    digital_write(MOTOR_B_GPIO_2, GPIO_HIGH);
    digital_write(MOTOR_B_GPIO_3, GPIO_LOW);
}

// TODO how to send PWM signal to control motor speed??
void control_forward() {
    // Set motor 1 forward
    digital_write(MOTOR_A_GPIO_1, GPIO_LOW);
    digital_write(MOTOR_A_GPIO_2, GPIO_HIGH);
    digital_write(MOTOR_A_GPIO_3, GPIO_HIGH);

    // Set motor 2 forward
    digital_write(MOTOR_B_GPIO_1, GPIO_LOW);
    digital_write(MOTOR_B_GPIO_2, GPIO_HIGH);
    digital_write(MOTOR_B_GPIO_3, GPIO_HIGH);
}


void control_back() {
    // Set motor 1 backward
    digital_write(MOTOR_A_GPIO_1, GPIO_HIGH);
    digital_write(MOTOR_A_GPIO_2, GPIO_LOW);
    digital_write(MOTOR_A_GPIO_3, GPIO_HIGH);

    // Set motor 2 backward
    digital_write(MOTOR_B_GPIO_1, GPIO_HIGH);
    digital_write(MOTOR_B_GPIO_2, GPIO_LOW);
    digital_write(MOTOR_B_GPIO_3, GPIO_HIGH);
}


// https://howtomechatronics.com/tutorials/arduino/arduino-dc-motor-control-tutorial-l298n-pwm-h-bridge/#:~:text=Next%20are%20the%20logic%20control,the%20motor%20will%20be%20disabled.
// TODO check coasting vs brakes
void control_brakes() {
    // Set motor 1 backward
    digital_write(MOTOR_A_GPIO_1, GPIO_LOW);
    digital_write(MOTOR_A_GPIO_2, GPIO_LOW);
    digital_write(MOTOR_A_GPIO_3, GPIO_HIGH);

    // Set motor 2 backward
    digital_write(MOTOR_B_GPIO_1, GPIO_LOW);
    digital_write(MOTOR_B_GPIO_2, GPIO_LOW);
    digital_write(MOTOR_B_GPIO_3, GPIO_HIGH);
}

void control_loop_main() {

}