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

extern shadow_cnode_t *post_capdl_shadow_cnode;
extern seL4_CPtr x86_ioport_ctrl_cptr;

uacpi_status uacpi_kernel_io_map(uacpi_io_addr base, uacpi_size len, uacpi_handle *out_handle)
{
    size_t new_ioport_cslot;
    if (!shadow_cnode_find_free_slot(post_capdl_shadow_cnode, &new_ioport_cslot)) {
        DEBUG_ACPI_ERR("out of CSlot\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    if (!len) {
        DEBUG_ACPI_ERR("len can't be zero\n");
        return UACPI_STATUS_INVALID_ARGUMENT;
    }

    seL4_Error err = seL4_X86_IOPortControl_Issue(x86_ioport_ctrl_cptr, base, base + len - 1,
                                                  shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, 0),
                                                  new_ioport_cslot, 58); // @billn dear Terry why 58??????
    if (err != seL4_NoError) {
        DEBUG_ACPI_ERR("failed to issue io port cap for base 0x%lx, len 0x%lx, seL4 error: %d\n", base, len, err);
        return UACPI_STATUS_MAPPING_FAILED;
    }

    shadow_cap_t shadow_cap = SHADOW_CNODE_MAKE_CAP(CAP_TYPE_X86_IO_PORT, base, base + len - 1, 0, 0); //@billn parent
    assert(shadow_cnode_insert_cap_at_slot(post_capdl_shadow_cnode, &shadow_cap, new_ioport_cslot));

    *out_handle = (uacpi_handle)(new_ioport_cslot);
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_read8(uacpi_handle handle, uacpi_size offset, uacpi_u8 *out_value)
{
    size_t cslot = (size_t)handle;
    shadow_cap_t *shadow_cap = shadow_cnode_get_cap_at_slot(post_capdl_shadow_cnode, (size_t)handle);
    assert(shadow_cap->type == CAP_TYPE_X86_IO_PORT);
    size_t base = shadow_cap->base_paddr;

    seL4_X86_IOPort_In8_t ret = seL4_X86_IOPort_In8(shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, cslot),
                                                    base + offset);
    if (ret.error != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", ret.error);
        return UACPI_STATUS_DENIED;
    }

    *out_value = (uacpi_u8)ret.result;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_read16(uacpi_handle handle, uacpi_size offset, uacpi_u16 *out_value)
{
    size_t cslot = (size_t)handle;
    shadow_cap_t *shadow_cap = shadow_cnode_get_cap_at_slot(post_capdl_shadow_cnode, cslot);
    assert(shadow_cap->type == CAP_TYPE_X86_IO_PORT);
    size_t base = shadow_cap->base_paddr;

    seL4_X86_IOPort_In16_t ret = seL4_X86_IOPort_In16(shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, cslot),
                                                      base + offset);
    if (ret.error != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", ret.error);
        return UACPI_STATUS_DENIED;
    }

    *out_value = (uacpi_u16)ret.result;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_read32(uacpi_handle handle, uacpi_size offset, uacpi_u32 *out_value)
{
    size_t cslot = (size_t)handle;
    shadow_cap_t *shadow_cap = shadow_cnode_get_cap_at_slot(post_capdl_shadow_cnode, cslot);
    assert(shadow_cap->type == CAP_TYPE_X86_IO_PORT);
    size_t base = shadow_cap->base_paddr;

    seL4_X86_IOPort_In32_t ret = seL4_X86_IOPort_In32(shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, cslot),
                                                      base + offset);
    if (ret.error != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", ret.error);
        return UACPI_STATUS_DENIED;
    }

    *out_value = (uacpi_u32)ret.result;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_write8(uacpi_handle handle, uacpi_size offset, uacpi_u8 in_value)
{
    size_t cslot = (size_t)handle;
    shadow_cap_t *shadow_cap = shadow_cnode_get_cap_at_slot(post_capdl_shadow_cnode, cslot);
    assert(shadow_cap->type == CAP_TYPE_X86_IO_PORT);
    size_t base = shadow_cap->base_paddr;

    seL4_Error err = seL4_X86_IOPort_Out8(shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, cslot), base + offset,
                                          in_value);
    if (err != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", err);
        return UACPI_STATUS_DENIED;
    }

    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_write16(uacpi_handle handle, uacpi_size offset, uacpi_u16 in_value)
{
    size_t cslot = (size_t)handle;
    shadow_cap_t *shadow_cap = shadow_cnode_get_cap_at_slot(post_capdl_shadow_cnode, cslot);
    assert(shadow_cap->type == CAP_TYPE_X86_IO_PORT);
    size_t base = shadow_cap->base_paddr;

    seL4_Error err = seL4_X86_IOPort_Out16(shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, cslot), base + offset,
                                           in_value);
    if (err != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", err);
        return UACPI_STATUS_DENIED;
    }

    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_io_write32(uacpi_handle handle, uacpi_size offset, uacpi_u32 in_value)
{
    size_t cslot = (size_t)handle;
    shadow_cap_t *shadow_cap = shadow_cnode_get_cap_at_slot(post_capdl_shadow_cnode, cslot);
    assert(shadow_cap->type == CAP_TYPE_X86_IO_PORT);
    size_t base = shadow_cap->base_paddr;

    seL4_Error err = seL4_X86_IOPort_Out32(shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, cslot), base + offset,
                                           in_value);
    if (err != seL4_NoError) {
        DEBUG_ACPI_ERR("seL4 error: %d\n", err);
        return UACPI_STATUS_DENIED;
    }

    return UACPI_STATUS_OK;
}

void uacpi_kernel_io_unmap(uacpi_handle handle)
{
    size_t cslot = (size_t)handle;
    shadow_cap_t *shadow_cap = shadow_cnode_get_cap_at_slot(post_capdl_shadow_cnode, cslot);
    assert(shadow_cap->type == CAP_TYPE_X86_IO_PORT);

    assert(seL4_CNode_Delete(shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, 0), (size_t)handle, 58)
           == seL4_NoError);
    assert(shadow_cnode_delete_cap_at_slot(post_capdl_shadow_cnode, (size_t)handle));
}
