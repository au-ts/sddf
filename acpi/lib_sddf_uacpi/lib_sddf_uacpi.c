/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include <sddf/util/printf.h>

bool sddf_uacpi_init(uint64_t rsdp_paddr)
{
    uacpi_status status = uacpi_initialize(UACPI_FLAG_BAD_CSUM_FATAL | UACPI_FLAG_BAD_TBL_SIGNATURE_FATAL);
    if (status != UACPI_STATUS_OK) {
        sddf_dprintf("Failed to initialise stage 1 of uACPI, error %u\n", status);
        return false;
    }

    return true;
}