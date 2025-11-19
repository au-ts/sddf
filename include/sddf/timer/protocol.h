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

// We use 32 bits because this fits any sane frequency in Hz
// (0-4.3GHz). All peripheral timers will usually be <200MHz.
// A larger frequency will break our common math, so we shouldn't
// force such values into this type anyway.
typedef uint32_t sddf_timer_freq_hz_t;


