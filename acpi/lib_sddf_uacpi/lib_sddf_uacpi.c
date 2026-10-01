/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include <uacpi/utilities.h>
#include <sddf/acpi/lib_sddf_uacpi.h>
#include <sddf/util/arch_timestamp_counter.h>
#include <sddf/util/printf.h>
#include <sddf/util/vspace.h>
#include <sddf/util/shadow_cnode.h>
#include <sddf/util/tlsf/tlsf.h>
#include "logging.h"

#define PAGE_SIZE_4K 0x1000

#define ACPI_HEAP_SIZE 0x400000
static alignas(8) char acpi_heap[ACPI_HEAP_SIZE];
static tlsf_t heap;

static shadow_cnode_t *post_capdl_shadow_cnode;
static seL4_CPtr vspace_cptr;
static seL4_CPtr x86_ioport_ctrl_cptr;

/* We map physical memory with vaddr as ACPI_DIRECT_MAP_BASE + requested paddr
 * so that we don't have to unmap it and do cap clean ups, since we will tear
 * everything down by the end anyways.

 * @billn improve by reserving this range in the linker? */
#define ACPI_DIRECT_MAP_BASE BIT(30)
#define MAX_PADDR_MAPPED 1024
static uint64_t paddr_mapped[MAX_PADDR_MAPPED];
static int num_p_mapped;

/* Annoyingly, seL4 give us the RSDP blob rather than the paddr, so we need
 * to copy it into a dummy "paddr" and serve it to uACPI from a buffer. */
#define RSDP_PADDR (ACPI_DIRECT_MAP_BASE - PAGE_SIZE_4K)
char rsdp_buf[PAGE_SIZE_4K];

uacpi_status uacpi_kernel_get_rsdp(uacpi_phys_addr *out_rsdp_address)
{
    DEBUG_ACPI("called\n");
    *out_rsdp_address = RSDP_PADDR;
    return UACPI_STATUS_OK;
}

void uacpi_kernel_log(uacpi_log_level log_level, const uacpi_char *s)
{
    sddf_dprintf(COLOUR_GREEN "uACPI: %s" COLOUR_RESET, s);
}

void *uacpi_kernel_map(uacpi_phys_addr addr, uacpi_size len)
{
    // DEBUG_ACPI("called with addr 0x%lx, len 0x%lx\n", addr, len);

    if (!len) {
        return NULL;
    }

    if (addr == RSDP_PADDR && len < PAGE_SIZE_4K) {
        return rsdp_buf;
    }

    uint64_t cur_paddr = ROUND_DOWN(addr, PAGE_SIZE_4K);
    uint64_t target_paddr_end = ROUND_UP(addr + len, PAGE_SIZE_4K);

    while (cur_paddr < target_paddr_end) {
        int i = 0;
        bool mapped = false;
        while (i < num_p_mapped) {
            if (paddr_mapped[i] == cur_paddr) {
                mapped = true;
                break;
            }
            i++;
        }

        if (!mapped) {
            if (num_p_mapped == MAX_PADDR_MAPPED) {
                DEBUG_ACPI_ERR("ran out of bookkeeping\n");
                return NULL;
            }

            if (map_memory_region(post_capdl_shadow_cnode, vspace_cptr, cur_paddr, PAGE_SIZE_4K,
                                  ACPI_DIRECT_MAP_BASE + cur_paddr, seL4_ReadWrite, seL4_X86_CacheDisabled)) {
                paddr_mapped[num_p_mapped] = cur_paddr;
                num_p_mapped++;
            } else {
                return NULL;
            }
        }

        cur_paddr += PAGE_SIZE_4K;
    }

    return (void *)(ACPI_DIRECT_MAP_BASE + addr);
}

void *uacpi_kernel_alloc(uacpi_size size)
{
    void *p = tlsf_malloc(heap, size);
    if (!p) {
        DEBUG_ACPI_ERR("out of heap memory, consider increasing ACPI_HEAP_SIZE\n");
    }
    return p;
}

void uacpi_kernel_free(void *mem)
{
    tlsf_free(heap, mem);
}

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
        DEBUG_ACPI_ERR("seL4 error: %d\n", ret.result);
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
        DEBUG_ACPI_ERR("seL4 error: %d\n", ret.result);
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
        DEBUG_ACPI_ERR("seL4 error: %d\n", ret.result);
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

uacpi_u64 uacpi_kernel_get_nanoseconds_since_boot(void)
{
    uint64_t freq = sddf_read_freq();
    if (!freq) {
        DEBUG_ACPI_ERR("TSC frequency unavailable, this function will return unimplemented to uACPI\n");
        return UACPI_STATUS_UNIMPLEMENTED;
    }

    return sddf_read_counter() / freq;
}

bool sddf_uacpi_init(sddf_uacpi_init_args_t *init_args)
{
    heap = tlsf_create_with_pool(acpi_heap, ACPI_HEAP_SIZE);
    if (!heap) {
        DEBUG_ACPI_ERR("Failed to initialise heap\n");
        return false;
    }

    memcpy(rsdp_buf, init_args->rsdp_blob, sizeof(acpi_rsdp_t));
    post_capdl_shadow_cnode = init_args->post_capdl_shadow_cnode;
    vspace_cptr = init_args->vspace_cptr;
    x86_ioport_ctrl_cptr = init_args->x86_ioport_ctrl_cptr;

    DEBUG_ACPI("Initialising uACPI...\n");
    /* Default settings for uACPI: enter ACPI mode on the platform, and don't error out if a table
     * checksum is bad in case the firmware have a bug. */
    uint64_t flags = 0;
    uacpi_status status = uacpi_initialize(flags);
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to initialise uACPI, error '%s'\n", uacpi_status_to_string(status));
        return false;
    }
    DEBUG_ACPI("uACPI initialised\n");

    DEBUG_ACPI("Executing DSDT and SSDTs...\n");
    status = uacpi_namespace_load();
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to parse and execute all DSDT and SSDT tables, error '%s'\n",
                       uacpi_status_to_string(status));
        return false;
    }
    DEBUG_ACPI("DSDT and SSDTs executed\n");

    DEBUG_ACPI("Initialising objects in namespaces...\n");
    status = uacpi_namespace_initialize();
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to initialise all objects in namespaces, error '%s'\n", uacpi_status_to_string(status));
        return false;
    }
    DEBUG_ACPI("Objects in namespaces initialised\n");

    DEBUG_ACPI("Setting interrupt model to I/O APIC...\n");
    status = uacpi_set_interrupt_model(UACPI_INTERRUPT_MODEL_IOAPIC);
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to set interrupt model to I/O APIC, error '%s'\n", uacpi_status_to_string(status));
        return false;
    }
    DEBUG_ACPI("Interrupt model set to I/O APIC\n");

    return true;
}

bool sddf_uacpi_deinit(void)
{
    return true;
}