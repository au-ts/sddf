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
#include "include/motor/motor_control.h"
#include "include/client/timer_queue.h"
#include "include/ultrasonic/ultrasonic_sensor.h"

/* Number of nanoseconds in a millisecond */
#define NS_IN_MS 1000000ULL
/* Number of nanoseconds in a microsecond */
#define NS_IN_US 1000ULL


/* Timeout IDs */
#define CLIENT_TIMEOUT_ID (0)
#define SENSOR_TIMEOUT_ID (1)
// Note: motor timeout IDs are the same as their gpio channel IDs
#define MOTOR_A_TIMEOUT_ID (5)
#define MOTOR_B_TIMEOUT_ID (6)
// Used to timeout duration of motor control
#define MOTOR_CONTROL_TIMEOUT_ID (4)

/* Shared Data */
extern sddf_channel timer_channel;
extern PriorityQueue timeout_queue;


/* Timer Helpers */
bool delay_microseconds(size_t microseconds, int timeout_id);
bool delay_miliseconds(size_t milliseconds, int timeout_id);
void set_timeout(uint64_t microseconds);
uint64_t get_time_now();