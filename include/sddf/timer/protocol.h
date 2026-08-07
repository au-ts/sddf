/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stdint.h>
#include <sddf/util/si_units.h>

/* Shared functionality/definitions between timer drivers and clients */

#define SDDF_TIMER_GET_TIME 0
#define SDDF_TIMER_SET_TIMEOUT 1
#define SDDF_TIMER_GET_COUNTER_FREQ 2

typedef uint64_t sddf_timer_freq_hz_t;
