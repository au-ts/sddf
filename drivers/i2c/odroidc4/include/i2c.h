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

#define I2C_MEM_OFFSET 0x22000


#define DRIVER_NOTIFY_ID 1  // Matching i2c.system

// PPC idenitifers
#define I2C_PPC_REQTYPE 1
#define I2C_PPC_CLAIM 1
#define I2C_PPC_RELEASE 2

// Security
#define I2C_SECURITY_LIST_SZ 127    // Supports one entry for each device
                                    // in standard 7-bit addressing
typedef i2c_addr_t i2c_security_list_t;

#endif