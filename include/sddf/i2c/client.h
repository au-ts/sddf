/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* By default we assume a 7-bit bus address. */
#ifndef I2C_BUS_ADDRESS_MAX
#define I2C_BUS_ADDRESS_MAX (0x7f)
#endif

#define I2C_BUS_SLOT (0)

/* Protected-Procedure-Call function idenitifers */
#define I2C_BUS_CLAIM       (1)
#define I2C_BUS_RELEASE     (2)

#define I2C_SUCCESS (0)
#define I2C_FAILURE (1)
