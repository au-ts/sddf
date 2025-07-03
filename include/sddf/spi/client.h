/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/spi/queue.h>

/* Helpers for interacting with the virtualiser. */
static inline bool spi_bus_claim(microkit_channel virt_ch, spi_cs_line_t cs_line, spi_cpol_t cpol, 
    spi_cpha_t cpha)
{

    microkit_msginfo claim = microkit_msginfo_new(SPI_BUS_CLAIM, SPI_BUS_CLAIM_ARGC);
    microkit_mr_set(SPI_BUS_SLOT, cs_line);
    microkit_mr_set(SPI_CPOL_SLOT, cpol);
    microkit_mr_set(SPI_CPHA_SLOT, cpha);
    microkit_msginfo ret = microkit_ppcall(virt_ch, claim);

    return microkit_msginfo_get_label(ret) == SPI_SUCCESS;
}

static inline bool spi_bus_release(microkit_channel virt_ch, spi_cs_line_t cs_line)
{
    microkit_msginfo msginfo = microkit_msginfo_new(SPI_BUS_RELEASE, SPI_BUS_RELEASE_ARGC);
    microkit_mr_set(SPI_BUS_SLOT, cs_line);
    msginfo = microkit_ppcall(virt_ch, msginfo);

    return microkit_msginfo_get_label(msginfo) == SPI_SUCCESS;
}
