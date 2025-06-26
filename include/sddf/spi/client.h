/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

#ifndef SPI_CS_LINES_MAX
#define SPI_CS_LINES_MAX 16
#endif

/* Argument Locations */
#define SPI_BUS_SLOT (0)
#define SPI_CPOL_SLOT (1)
#define SPI_CPHA_SLOT (2)

/* Virt Protected-Procedure-Call function idenitifers */
#define SPI_BUS_CLAIM (1)
#define SPI_BUS_RELEASE (2)
#define SPI_BUS_CLAIM_ARGC (3)
#define SPI_BUS_RELEASE_ARGC (1)

/* Driver Protected-Procedure-Call function identifers */
#define SPI_BUS_CONFIG (3)
#define SPI_BUS_CONFIG_ARGC (3)

/* Clock Polarities */
#define SPI_CPOL_LOW (0)
#define SPI_CPOL_HIGH (1)

/* Clock Phase */
#define SPI_CPHA_FIRST (0)
#define SPI_CPHA_SECOND (1)

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
