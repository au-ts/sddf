/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

/* By default we assume a 7-bit bus address. */
#ifndef I2C_BUS_ADDRESS_MAX
#define I2C_BUS_ADDRESS_MAX (0x7f)
#endif

#define I2C_BUS_SLOT (0)

/* Protected-Procedure-Call function idenitifers */
#define I2C_BUS_CLAIM       (1)
#define I2C_BUS_RELEASE     (2)

/* This is the label of the PPC response from the virtualiser */
#define I2C_SUCCESS (0)
#define I2C_FAILURE (1)

/* Helpers for interacting with the virutaliser. */
static inline bool i2c_bus_claim(microkit_channel virt_ch, size_t bus_address)
{
    microkit_msginfo msginfo = microkit_msginfo_new(I2C_BUS_CLAIM, 1);
    microkit_mr_set(I2C_BUS_SLOT, bus_address);
    msginfo = microkit_ppcall(virt_ch, msginfo);

    return microkit_msginfo_get_label(msginfo) == I2C_SUCCESS;
}

static inline bool i2c_bus_release(microkit_channel virt_ch, size_t bus_address)
{
    microkit_msginfo msginfo = microkit_msginfo_new(I2C_BUS_RELEASE, 1);
    microkit_mr_set(I2C_BUS_SLOT, bus_address);
    msginfo = microkit_ppcall(virt_ch, msginfo);

    return microkit_msginfo_get_label(msginfo) == I2C_SUCCESS;
}
