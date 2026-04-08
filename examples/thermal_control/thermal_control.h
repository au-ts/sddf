/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <sddf/tmu/protocol.h>

#define FAN_FREQ (5000)

typedef struct trip_point {
    sddf_temp_celsius_t temp_lower_bound;   // switch when temperature hits this
    op_point_idx_t dvfs_opp;
    uint64_t fan_pwm_duty;
} trip_point_t;
