/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#define CONTROL_STOP (0)
#define CONTROL_FORWARD (1)
#define CONTROL_REVERSE (2)
#define CONTROL_NEUTRAL (3)

#define REQUEST_STOP (0)
#define REQUEST_FORWARD (1)
#define REQUEST_BACK (2)
#define REQUEST_LEFT (3)
#define REQUEST_RIGHT (4)
#define REQUEST_NEUTRAL (5)


// PWM Delays
#define PWM_CHANNEL_MAPPING_COLS 3
#define PWM_CHANNEL_MAPPING_ROWS 3

#define PWM_TIME_HIGH 1
#define PWM_TIME_LOW 2

// Time Spent (microseconds) on HIGH/LOW for Motor Control PWM Signals
// Control, Time HIGH, Time LOW
static const int pwm_delay_mappings[PWM_CHANNEL_MAPPING_COLS][PWM_CHANNEL_MAPPING_ROWS] = {
    {CONTROL_FORWARD, 2000, 18000},
    {CONTROL_REVERSE,  1000, 19000},
    {CONTROL_NEUTRAL, 1500, 18500},
};




