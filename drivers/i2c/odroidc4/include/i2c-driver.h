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

#define TOKEN_LIST_MAX 128
#define WBUF_SZ_MAX 64
#define RBUF_SZ_MAX 64

// Internal driver state for each bus
typedef struct _i2c_bus_state {
    uint16_t speed;         // Current programmed speed. Note that this stores the
                            // actual speed, not the quarter clock delay.   
} i2c_bus_t;


typedef uint8_t i2c_addr_t;         // 7-bit addressing


// Driver-server interface
#include "i2c-token.h"
#define SERVER_NOTIFY_ID 1


#endif