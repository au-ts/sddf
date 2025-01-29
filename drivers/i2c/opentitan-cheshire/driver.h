/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// driver.h
// sDDF-related includes for OpenTitan I2C driver.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 01/2025

#pragma once
#include <stdint.h>
#include <stddef.h>

#define DATA_REGIONS_START 0x10000000

typedef uint8_t data_direction_t;
enum data_direction {
    DATA_DIRECTION_WRITE = 0x0,
    DATA_DIRECTION_READ = 0x1,
    DATA_DIRECTION_READC = 0x3, // data_direction & 1 is true if reading
};

typedef struct _i2c_ifState {
    /* Pointer to current request/response being handled */
    uint8_t *curr_data;
    /* Number of bytes in current request (number of tokens) */
    int curr_request_len;
    /* Number of bytes in current response (only the data) and not the error tokens at the start */
    int curr_response_len;
    /* Index into current buffer */
    uint64_t req_idx;
    /* Flag indicating that there is more independent requests waiting on the queue_handle.request. */
    bool notified;

    /* I2C bus address of the current request being handled */
    uint8_t addr;

    // Interval control
    /* Number of bytes to read/write if request data offset is in the midst of a buffer. If this is
       zero, no read/write is in progress and we can interpret the current byte as a token.*/
    uint8_t interval_remaining;
    data_direction_t data_direction;
    bool int_has_stop;
    bool int_has_start;
} i2c_ifState_t;

static inline void opentitan_i2c_reset_state(i2c_ifState_t *state) {
    state->curr_data = (uint8_t *) 0;
    state->curr_request_len = 0;
    state->curr_response_len = 0;
    state->req_idx = 0;
    state->notified = false;
    state->interval_remaining= 0;
    state->data_direction = DATA_DIRECTION_WRITE;
    state->addr = 0;
    state->int_has_stop = false;
}
