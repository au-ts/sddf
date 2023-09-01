/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// pn532.c
// Extremely minimal driver for the PN532 NFC chip. Only supports I2C.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#include <sel4cp.h>
#include "i2c.h"


// PN532 I2C address
#define PN532_I2C_ADDRESS   (0x48 >> 1)
