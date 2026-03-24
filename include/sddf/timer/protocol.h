/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stdint.h>
#include <sddf/util/si_units.h>

// Client-virt interaction
typedef enum {
    SDDF_TIMER_GET_TIME = 0U,
    SDDF_TIMER_REQ_TIMEOUT,
    SDDF_TIMER_CANCEL_TIMEOUT
} sddf_timer_ppc_codes_t;

typedef enum {
    SDDF_TIMER_ERR_OK = 0U,
    SDDF_TIMER_ERR_UNAVAILABLE, // no capacity
    SDDF_TIMER_ERR_EINVAL,     // invalid args
    SDDF_TIMER_ERR_PCC      // bogus PPC
} sddf_timer_err_t;

// lower than this will be noisy with lower freq timers and means PPC delays are notable!
#define SDDF_TIMER_MIN_PERIOD_NS (1000)

// MR mappings for each call. Error state always in label.
// REQ_TIMEOUT
#define SDDF_TIMER_REQ_TIMEOUT_TIMEOUT (0) // mr0
#define SDDF_TIMER_REQ_TIMEOUT_PERIOD  (1) // mr1 - period in ns. If zero, not periodic.
#define SDDF_TIMER_REQ_TIMEOUT_RET_ID  (0) // mr0 - ID of timer, used to cancel.

// CANCEL_TIMEOUT
#define SDDF_TIMER_CANCEL_TIMEOUT_ID   (0) // mr0. ID of timer to cancel.

// Virt-driver interaction
#define SDDF_TIMER_VIRT_GET_TIME 0
#define SDDF_TIMER_VIRT_SET_TIMEOUT 1

// We use 32 bits because this fits any sane frequency in Hz
// (0-4.3GHz). All peripheral timers will usually be <200MHz.
// A larger frequency will break our common math, so we shouldn't
// force such values into this type anyway.
typedef uint32_t sddf_timer_freq_hz_t;

/**
 * Get the last timeout that fired from the time page.
 * This is just a utility function to hide interacting with
 * the time page directly.
 *
 * The time page has the following properties:
 *  -> updated whenever the timer driver finishes servicing a timeout for the current client
 *  -> does not contain current time.
 */
inline uint64_t read_time_page(uint64_t *time_page)
{
   return (*time_page);
}
