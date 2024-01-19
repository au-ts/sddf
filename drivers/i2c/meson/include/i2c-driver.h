/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// i2c-driver.h
// Header containing all generic features for I2C drivers targeting the
// sDDF and seL4 core platform.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#ifndef I2C_DRIVER_H
#define I2C_DRIVER_H

#define ODROIDC4

#include <stdint.h>
#include "i2c-transport.h"
#include "gpio.h"
#include "clk.h"
#include <stdint.h>
#include "printf.h"
#include <sddf/util/fence.h>
#include "i2c.h"

#define TOKEN_LIST_MAX 128
#define WBUF_SZ_MAX 64
#define RBUF_SZ_MAX 64

// Driver state
typedef struct _i2c_ifState {
    req_buf_ptr_t current_req; // Pointer to current request.
    ret_buf_ptr_t current_ret; // Pointer to current return buf.
    int current_ret_len;        // Number of bytes in current return.
    int current_req_len;        // Number of bytes in current request.
    size_t remaining;              // Number of bytes remaining to dispatch.
    int notified;               // Flag indicating that there is more work waiting.
    int data_direction;                    // Data direction. 0 = write, 1 = read.
} i2c_ifState_t;

#define DATA_DIRECTION_WRITE (0x0)
#define DATA_DIRECTION_READ (0x1)


// Driver-server interface
#include "i2c-token.h"
#define SERVER_NOTIFY_ID 1


#endif
