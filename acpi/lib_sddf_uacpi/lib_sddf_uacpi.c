/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include <sddf/util/printf.h>
#include <sddf/util/tlsf/tlsf.h>
#include "logging.h"

#define ACPI_HEAP_SIZE 0x400000
alignas(8) char acpi_heap[ACPI_HEAP_SIZE];
tlsf_t heap;

uint64_t rsdp_phys_addr;

uacpi_status uacpi_kernel_get_rsdp(uacpi_phys_addr *out_rsdp_address)
{
    DEBUG_ACPI("called\n");
    *out_rsdp_address = rsdp_phys_addr;
    return UACPI_STATUS_OK;
}

bool sddf_uacpi_init(uint64_t rsdp_paddr)
{
    heap = tlsf_create_with_pool(acpi_heap, ACPI_HEAP_SIZE);
    if (!heap) {
        DEBUG_ACPI_ERR("Failed to initialise heap\n");
        return false;
    }

    rsdp_phys_addr = rsdp_paddr;

    DEBUG_ACPI("calling uacpi_initialize()\n");
    uacpi_status status = uacpi_initialize(UACPI_FLAG_BAD_CSUM_FATAL | UACPI_FLAG_BAD_TBL_SIGNATURE_FATAL);
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to initialise stage 1 of uACPI, error %u\n", status);
        return false;
    }

    return true;
}