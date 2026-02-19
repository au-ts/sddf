/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <os/sddf.h>
#include <sddf/timer/config.h>
#include <sddf/gpio/client.h>
#include <sddf/gpio/config.h>
#include <sddf/gpio/protocol.h>


#include "include/gpio_common/gpio_common.h"
#include "include/motor/motor_control.h"
#include "include/client/timer_queue.h"
#include "include/ultrasonic/ultrasonic_sensor.h"

/* Number of nanoseconds in a millisecond */
#define NS_IN_MS 1000000ULL
/* Number of nanoseconds in a microsecond */
#define NS_IN_US 1000ULL

/* Timeout IDs */
// Used to timeout duration of motor control
#define MOTOR_CONTROL_TIMEOUT_ID (5)
#define CLIENT_TIMEOUT_ID (6)
#define SENSOR_TIMEOUT_ID (7)

/* Shared Data */
extern sddf_channel timer_channel;
extern sddf_channel gpio_channel_motor_a;
extern sddf_channel gpio_channel_motor_b;
extern sddf_channel gpio_channel_echo;
extern sddf_channel gpio_channel_trigger;

extern PriorityQueue timeout_queue;


/* Timer Helpers */
bool delay_microseconds(size_t microseconds, int timeout_id);
bool delay_miliseconds(size_t milliseconds, int timeout_id);
void set_timeout(uint64_t microseconds);
uint64_t get_time_now();