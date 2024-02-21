/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// API for clients of I2C server
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 09/2023


#ifndef __I2C_SEL4CP_H__
#define __I2C_SEL4CP_H__

#include "i2c.h"
#include <stdint.h>

typedef struct i2cAddr {
    uint8_t addr;
    uint8_t bus;
} i2cAddr_t;

/**
 * Write the contents of a supplied buffer to the i2c device
 * specified by addr.
 * @param addr Address struct for target device, specifying bus and addr.
 * @param data Pointer to buffer containing data to write.
 * @param len Length of data to write.
 * @return 0 on success, -1 on failure.
*/
int i2c_write(i2cAddr_t *addr, uint8_t *data, uint32_t len);

/**
 * Read the contents of a supplied buffer from the i2c device.
 * @param addr Address struct for target device, specifying bus and addr.
 * @param data Pointer to buffer to store read data.
 * @param len Length of data to read.
 * @return 0 on success, -1 on failure.
*/
int i2c_read(i2cAddr_t *addr, uint8_t *data, uint32_t len);

/**
 * Write a single byte before reading from the i2c device. Used for subaddressing.
 * @param addr Address struct for target device, specifying bus and addr.
 * @param wdata Data to write. Usually the address of a device register.
 * @param rdata Pointer to buffer to store read data.
 * @param len Length of data to read.
 * @return 0 on success, -1 on failure.
*/
int i2c_writeread(i2cAddr_t *addr, uint8_t wdata, uint8_t *rdata, uint32_t len);

#endif