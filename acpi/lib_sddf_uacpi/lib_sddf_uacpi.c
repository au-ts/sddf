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
#include <sddf/util/cspace.h>
#include <sddf/util/tlsf/tlsf.h>
#include "logging.h"

#define PAGE_SIZE_4K 0x1000

#define ACPI_HEAP_SIZE 0x400000
static alignas(8) char acpi_heap[ACPI_HEAP_SIZE];
static tlsf_t heap;

static cnode_specs_t *ut_cnode;

/* We map physical memory with vaddr as ACPI_DIRECT_MAP_BASE + requested paddr
 * so that we don't have to unmap it and do cap clean ups, since we will tear
 * everything down by the end anyways. */
#define ACPI_DIRECT_MAP_BASE BIT(32)
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
    DEBUG_ACPI("called with addr 0x%lx, len 0x%lx\n", addr, len);

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

            if (map_memory_region(ut_cnode, cur_paddr, PAGE_SIZE_4K, ACPI_DIRECT_MAP_BASE + cur_paddr)) {
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
    return tlsf_malloc(heap, size);
}

void uacpi_kernel_free(void *mem)
{
    tlsf_free(heap, mem);
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
    ut_cnode = init_args->ut_cnode;

    DEBUG_ACPI("Initialising uACPI...\n");
    /* We don't enter ACPI mode to avoid uACPI from requesting I/O Port mappings.
     * This is sound because we don't care about any power management or embedded controller stuff. */
    uint64_t flags = UACPI_FLAG_NO_ACPI_MODE;
    uacpi_status status = uacpi_initialize(flags);
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to initialise uACPI, error '%s'\n", uacpi_status_to_string(status));
        return false;
    }
    DEBUG_ACPI("uACPI initialised\n");

    DEBUG_ACPI("Executing DSDT and SSDTs...\n");
    status = uacpi_namespace_load();
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to parse and execute all DSDT and SSDT tables, error '%s'\n", uacpi_status_to_string(status));
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