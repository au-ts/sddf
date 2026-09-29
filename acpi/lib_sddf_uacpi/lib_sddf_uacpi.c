/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include <sddf/acpi/lib_sddf_uacpi.h>
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

void uacpi_kernel_unmap(void *addr, uacpi_size len)
{
    /* no-op */
}

void *uacpi_kernel_alloc(uacpi_size size)
{
    DEBUG_ACPI("called with size %lu\n", size);
    return tlsf_malloc(heap, size);
}

void uacpi_kernel_free(void *mem)
{
    DEBUG_ACPI("called\n");
    tlsf_free(heap, mem);
}

static uint8_t mutex;

uacpi_handle uacpi_kernel_create_mutex(void)
{
    DEBUG_ACPI("called\n");
    return &mutex;
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

    DEBUG_ACPI("calling uacpi_initialize()\n");
    uacpi_status status = uacpi_initialize(0);
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to initialise stage 1 of uACPI, error '%s'\n", uacpi_status_to_string(status));
        return false;
    }

    return true;
}

bool sddf_uacpi_deinit(void)
{
    return true;
}