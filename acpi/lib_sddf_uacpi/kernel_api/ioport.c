/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include <uacpi/acpi.h>
#include <uacpi/utilities.h>
#include <sddf/acpi/lib_sddf_uacpi.h>
#include <sddf/util/printf.h>
#include <sddf/util/shadow_cnode.h>
#include <sddf/util/tlsf/tlsf.h>
#include "../logging.h"
#include "../types.h"

extern lib_sddf_uacpi_state_t lib_state;

typedef struct {
    uacpi_io_addr base;
} io_port_handle_t;

static seL4_CPtr io_port_master_cptr(void)
{
    return shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, lib_state.x86_ioport_master_cslot);
}

static uacpi_io_addr base_from_handle(uacpi_handle handle)
{
    return ((io_port_handle_t *)handle)->base;
}

uacpi_status uacpi_kernel_io_map(uacpi_io_addr base, uacpi_size len, uacpi_handle *out_handle)
{
    io_port_handle_t *handle = tlsf_malloc(lib_state.acpi_heap, sizeof(io_port_handle_t));
    if (!handle) {
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    handle->base = base;
    *out_handle = (uacpi_handle)(handle);
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_read8(uacpi_handle handle, uacpi_size offset, uacpi_u8 *out_value)
{
    seL4_X86_IOPort_In8_t ret = seL4_X86_IOPort_In8(io_port_master_cptr(), base_from_handle(handle) + offset);
    if (ret.error != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", ret.error);
        return UACPI_STATUS_DENIED;
    }

    *out_value = (uacpi_u8)ret.result;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_read16(uacpi_handle handle, uacpi_size offset, uacpi_u16 *out_value)
{
    seL4_X86_IOPort_In16_t ret = seL4_X86_IOPort_In16(io_port_master_cptr(), base_from_handle(handle) + offset);
    if (ret.error != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", ret.error);
        return UACPI_STATUS_DENIED;
    }

    *out_value = (uacpi_u16)ret.result;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_read32(uacpi_handle handle, uacpi_size offset, uacpi_u32 *out_value)
{
    seL4_X86_IOPort_In32_t ret = seL4_X86_IOPort_In32(io_port_master_cptr(), base_from_handle(handle) + offset);
    if (ret.error != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", ret.error);
        return UACPI_STATUS_DENIED;
    }

    *out_value = (uacpi_u32)ret.result;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_write8(uacpi_handle handle, uacpi_size offset, uacpi_u8 in_value)
{
    seL4_Error err = seL4_X86_IOPort_Out8(io_port_master_cptr(), base_from_handle(handle) + offset, in_value);
    if (err != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", err);
        return UACPI_STATUS_DENIED;
    }

    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_write16(uacpi_handle handle, uacpi_size offset, uacpi_u16 in_value)
{
    seL4_Error err = seL4_X86_IOPort_Out16(io_port_master_cptr(), base_from_handle(handle) + offset, in_value);
    if (err != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", err);
        return UACPI_STATUS_DENIED;
    }

    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_write32(uacpi_handle handle, uacpi_size offset, uacpi_u32 in_value)
{
    seL4_Error err = seL4_X86_IOPort_Out32(io_port_master_cptr(), base_from_handle(handle) + offset, in_value);
    if (err != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", err);
        return UACPI_STATUS_DENIED;
    }

    return UACPI_STATUS_OK;
}

void uacpi_kernel_io_unmap(uacpi_handle handle)
{
    tlsf_free(lib_state.acpi_heap, handle);
}
