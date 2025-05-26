/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

#define SPI_BUS_SLOT (0)

/* Protected-Procedure-Call function idenitifers */
#define SPI_BUS_CLAIM       (1)
#define SPI_BUS_RELEASE     (2)

/* This is the label of the PPC response from the virtualiser */
#define SPI_SUCCESS (0)
#define SPI_FAILURE (1)

/* Helpers for interacting with the virtualiser. */
static inline bool spi_bus_claim(microkit_channel virt_ch, uint8_t bus_address)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SPI_BUS_CLAIM, 1);
    microkit_mr_set(SPI_BUS_SLOT, bus_address);
    msginfo = microkit_ppcall(virt_ch, msginfo);

    return microkit_msginfo_get_label(msginfo) == SPI_SUCCESS;
}

static inline bool spi_bus_release(microkit_channel virt_ch, uint8_t bus_address)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SPI_BUS_RELEASE, 1);
    microkit_mr_set(SPI_BUS_SLOT, bus_address);
    msginfo = microkit_ppcall(virt_ch, msginfo);

    return microkit_msginfo_get_label(msginfo) == SPI_SUCCESS;
}
