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

#define DRIVER_NOTIFY_ID    1


// Tranposrt layer
#define I2C_BUF_SZ 512
#define I2C_BUF_COUNT 511

// PPC interface for server - used to allocate/drop addresses
// PPC MR slots
#define I2C_PPC_MR_REQTYPE  0   // arg0: request or release.
#define I2C_PPC_MR_ADDR     1   // arg1: i2c address to claim.
#define I2C_PPC_MR_CID      2   // arg2: channel id of client to server.
                                //       DANGER: this is the client ID as the server
                                //       sees it.
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
