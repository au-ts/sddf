

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

uintptr_t control_buffer_base_vaddr;

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

#define TIMER_CHANNEL (1)
#define MOTOR_CONTROL_CHANNEL (2)

// TODO Do a coroutine while motor control (to block current control requests)
// Whether there is unfulfilled motor control request
int is_ongoing_request = 0;

bool delay_ms(size_t milliseconds)
{
    size_t time_ns = milliseconds * NS_IN_MS;

    /* Detect potential overflow */
    if (milliseconds != 0 && time_ns / milliseconds != NS_IN_MS) {
        LOG_CLIENT_ERR("overflow detected in delay_ms");
        return false;
    }

    sddf_timer_set_timeout(TIMER_CHANNEL, time_ns);
    co_switch(t_event);

    return true;
}


void append_control_buffer(int command) {
    *REG_PTR(control_buffer_base_vaddr, UARTDR) = command;
} 

void send_forward_request() {
    append_control_buffer(CONTROL_FORWARD);
    microkit_notify(MOTOR_CONTROL_CHANNEL);
}

void send_reverse_request() {
    append_control_buffer(CONTROL_REVERSE);
    microkit_notify(MOTOR_CONTROL_CHANNEL);
}

void send_neutral_request() {
    append_control_buffer(CONTROL_NEUTRAL);
    microkit_notify(MOTOR_CONTROL_CHANNEL);
}

void client_main(void) {
    send_forward_request();
    delay_ms(20000);

    send_reverse_request();
    delay_ms(20000);
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
    LOG_CLIENT("Init\n");

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

