/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>

#define SDDF_PWM_SET_FANSPEED 0

enum FanSpeed {
    Stopped = 0,
    Low = 64,
    Medium = 128,
    High = 192,
    Full = 255,
};

static inline void sddf_pwm_fan_speed(unsigned int channel, FanSpeed speed)
{
    sddf_set_mr(0, speed);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PWM_SET_FANSPEED, 0, 0, 1));
}