/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// i2c.h
// Header file for the I2C server.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#ifndef I2C_H
#define I2C_H
#include "sw_shared_ringbuffer.h"
typedef uint8_t i2c_addr_t;         // 7-bit addressing

#define DRIVER_NOTIFY_ID    1  // Matching i2c.system
#define I2C_NUM_BUSES       4  // Number of i2c buses supported


// PPC MR slots
#define I2C_PPC_MR_REQTYPE  0
#define I2C_PPC_MR_BUS      1
#define I2C_PPC_MR_ADDR     2
// PPC idenitifers
#define I2C_PPC_CLAIM       1
#define I2C_PPC_RELEASE     2

// Security
#define I2C_SECURITY_LIST_SZ 127    // Supports one entry for each device
                                    // in standard 7-bit addressing
typedef int8_t i2c_security_list_t; // -1 = unclaimed. Otherwise, 7-bit i2c address.
                                    // I2C addresses are 7 bit so signing an 8 bit int
                                    // is fine.


// Client<=>Server interface
// Shared memory regions
extern uintptr_t client_req_free;
extern uintptr_t client_req_used;
extern uintptr_t client_ret_free;
extern uintptr_t client_ret_used;

void i2c_init(int buf_init);

int clientRequest(int bus, size_t size, uint8_t *data, uint8_t client, uint8_t addr);

#endif