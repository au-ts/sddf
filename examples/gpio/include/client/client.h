/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>

/* Number of nanoseconds in a millisecond */
#define NS_IN_MS 1000000ULL
/* Number of nanoseconds in a microsecond */
#define NS_IN_US 1000ULL


/* Timeout IDs */
#define CLIENT_TIMEOUT_ID (0)
#define SENSOR_TIMEOUT_ID (1)
// Note: motor timeout IDs are the same as their gpio channel IDs
#define MOTOR_A_TIMEOUT_ID (2)
#define MOTOR_B_TIMEOUT_ID (3)
// Used to timeout duration of motor control
#define MOTOR_CONTROL_TIMEOUT_ID (4)


/* Timer Helpers */
bool delay_microsec(size_t microseconds, int timeout_id);
bool delay_ms(size_t milliseconds, int timeout_id);
uint64_t get_time_now();