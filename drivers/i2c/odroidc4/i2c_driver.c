/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
// i2c.c
// i2c driver wrapper. Redirects to device appropriate driver.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

// Hardkernel ODROID C4 SBC
#ifdef ODROIDC4
#include "i2c-odroid-c4.c"
// Generic driver for implementation reference
#else
#endif
