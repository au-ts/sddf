

/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include "include/client/client.h"
#include "include/motor/motor_control.h"

#define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_printf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// Motor control buffers
uintptr_t control_buffer_base_vaddr_a;
uintptr_t control_buffer_base_vaddr_b;
uintptr_t ultrasonic_input_buffer_base_vaddr;
uintptr_t ultrasonic_output_buffer_base_vaddr;

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

// Channels
#define TIMER_CHANNEL (1)
#define MOTOR_CONTROL_A_CHANNEL (2)
#define MOTOR_CONTROL_B_CHANNEL (3)
#define ULTRASONIC_CHANNEL (4)

// Unfulfilled motor control request
int is_ongoing_request = 0;

bool delay_ms(size_t milliseconds)
{
    size_t time_ns = milliseconds * NS_IN_MS;

    /* Detect potential overflow */
    if (milliseconds != 0 && time_ns / milliseconds != NS_IN_MS) {
        LOG_CLIENT_ERR("overflow detected in delay_ms\n");
        return false;
    }

    sddf_timer_set_timeout(TIMER_CHANNEL, time_ns);
    co_switch(t_event);

    return true;
}

void append_control_buffer(int command, uintptr_t vaddr) {
    *REG_PTR(vaddr, UARTDR) = command;
} 

void send_forward_request(int motor_ch) {
    if (motor_ch == MOTOR_CONTROL_A_CHANNEL) {
        append_control_buffer(CONTROL_FORWARD, control_buffer_base_vaddr_a);
    }
    else if (motor_ch == MOTOR_CONTROL_B_CHANNEL) {
        append_control_buffer(CONTROL_FORWARD, control_buffer_base_vaddr_b);
    }
    LOG_CLIENT("Sending forward request\n");
    microkit_notify(motor_ch);
}

void send_reverse_request(int motor_ch) {
    if (motor_ch == MOTOR_CONTROL_A_CHANNEL) {
        append_control_buffer(CONTROL_REVERSE, control_buffer_base_vaddr_a);
    }
    else if (motor_ch == MOTOR_CONTROL_B_CHANNEL) {
        append_control_buffer(CONTROL_REVERSE, control_buffer_base_vaddr_b);
    }
    LOG_CLIENT("Sending reverse request\n");
    microkit_notify(motor_ch);
}

void send_neutral_request(int motor_ch) {
    if (motor_ch == MOTOR_CONTROL_A_CHANNEL) {
        append_control_buffer(CONTROL_NEUTRAL, control_buffer_base_vaddr_a);
    }
    else if (motor_ch == MOTOR_CONTROL_B_CHANNEL) {
        append_control_buffer(CONTROL_NEUTRAL, control_buffer_base_vaddr_b);
    }
    LOG_CLIENT("Sending neutral request\n");
    microkit_notify(motor_ch);
}

// returns distance in cm
uint64_t get_ultrasonic_reading() {
    microkit_msginfo new_msg = microkit_msginfo_new(0, 0);
    microkit_msginfo res = microkit_ppcall(ULTRASONIC_CHANNEL, new_msg);
    uint64_t distance = microkit_mr_get(0);
    return distance;
}

// TODO check these
void drive_forward(void) {
    send_forward_request(MOTOR_CONTROL_A_CHANNEL);
    send_forward_request(MOTOR_CONTROL_B_CHANNEL);
}

void drive_reverse(void) {
    send_reverse_request(MOTOR_CONTROL_A_CHANNEL);
    send_reverse_request(MOTOR_CONTROL_B_CHANNEL);
}

void drive_left(void) {
    send_forward_request(MOTOR_CONTROL_A_CHANNEL);
    send_neutral_request(MOTOR_CONTROL_B_CHANNEL);
}

void drive_right(void) {
    send_forward_request(MOTOR_CONTROL_B_CHANNEL);
    send_neutral_request(MOTOR_CONTROL_A_CHANNEL);
}

void client_main(void) {
    LOG_CLIENT("In client main\n");
    drive_forward();
    delay_ms(5000);

    drive_left();
    delay_ms(5000);

    drive_right();
    delay_ms(5000);

    drive_reverse();
    delay_ms(5000);
}

// Call coroutine, block other commands from executing
void notified(microkit_channel ch) {
    // check this switch
    switch (ch)
    {
    case TIMER_CHANNEL:
        co_switch(t_main);
        break;
    default:
        LOG_CLIENT("Unexpected channel call\n");
        break;
    }
}

void init(void) {
    // LOG_CLIENT("Init\n");

    // /* Define the event loop/notified thread as the active co-routine */
    // t_event = co_active();

    // /* derive main entry point */
    // t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    // co_switch(t_main);
}

