/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include <uacpi/acpi.h>
#include <uacpi/tables.h>
#include <uacpi/utilities.h>
#include <sddf/acpi/lib_sddf_uacpi.h>
#include <sddf/util/arch_timestamp_counter.h>
#include <sddf/util/printf.h>
#include <sddf/util/vspace.h>
#include <sddf/util/shadow_cnode.h>
#include <sddf/util/tlsf/tlsf.h>
#include <sddf/timer/timer_common.h>
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

typedef struct {
    void *vaddr;
    uint64_t paddr;
    size_t size_bytes;
    uint16_t segment;
    uint8_t start_bus;
    uint8_t end_bus;
} ecam_desc_t;

#define MAX_NUM_ECAM 4
static ecam_desc_t ecams[MAX_NUM_ECAM];
static size_t num_ecams = 0;
static uint64_t next_avail_ecam_vaddr = BIT(27);
#define MAX_ECAM_VADDR ACPI_DIRECT_MAP_BASE

typedef struct {
    void *config_space_vaddr; // in one of the ECAM
} pci_device_uacpi_handle_t;

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

            if (map_memory_region(post_capdl_shadow_cnode, vspace_cptr, cur_paddr, PAGE_SIZE_4K, false,
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

uacpi_status uacpi_kernel_pci_device_open(uacpi_pci_address address, uacpi_handle *out_handle)
{
    // @billn handle when firmware did not provide mcfg
    int ecam_idx = 0;
    for (; ecam_idx < num_ecams; ecam_idx++) {
        if (address.segment == ecams[ecam_idx].segment && address.bus >= ecams[ecam_idx].start_bus
            && address.bus <= ecams[ecam_idx].end_bus) {
            break;
        }
    }

    if (ecam_idx == MAX_NUM_ECAM) {
        DEBUG_ACPI_ERR("failed to find matching ECAM for %u:%u.%u in PCI segment %u\n", address.bus, address.device,
                       address.function, address.segment);
        return UACPI_STATUS_NOT_FOUND;
    }

    // @billn this is a bit sus when start bus != 0
    void *config_space_vaddr = (void *)((uintptr_t)(ecams[ecam_idx].vaddr)
                                        + ((uint64_t)address.bus << 20 | (uint64_t)address.device << 15
                                           | (uint64_t)address.function << 12));

    pci_device_uacpi_handle_t *handle = tlsf_malloc(heap, sizeof(pci_device_uacpi_handle_t));
    if (!handle) {
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    handle->config_space_vaddr = config_space_vaddr;
    *out_handle = handle;

    return UACPI_STATUS_OK;
}

void uacpi_kernel_pci_device_close(uacpi_handle handle)
{
    tlsf_free(heap, handle);
}

uacpi_status uacpi_kernel_pci_read8(uacpi_handle device, uacpi_size offset, uacpi_u8 *value)
{
    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint8_t *reg = (uint8_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *value = *reg;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_read16(uacpi_handle device, uacpi_size offset, uacpi_u16 *value)
{
    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint16_t *reg = (uint16_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *value = *reg;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_read32(uacpi_handle device, uacpi_size offset, uacpi_u32 *value)
{
    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint32_t *reg = (uint32_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *value = *reg;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_write8(uacpi_handle device, uacpi_size offset, uacpi_u8 value)
{
    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint8_t *reg = (uint8_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *reg = value;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_write16(uacpi_handle device, uacpi_size offset, uacpi_u16 value)
{
    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint16_t *reg = (uint16_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *reg = value;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_write32(uacpi_handle device, uacpi_size offset, uacpi_u32 value)
{
    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint32_t *reg = (uint32_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *reg = value;
    return UACPI_STATUS_OK;
}

uacpi_u64 uacpi_kernel_get_nanoseconds_since_boot(void)
{
    uint64_t freq = sddf_read_freq();
    if (!freq) {
        DEBUG_ACPI_ERR("TSC frequency unavailable, this function will return unimplemented to uACPI\n");
        return UACPI_STATUS_UNIMPLEMENTED;
    }

    return ticks_to_ns(sddf_read_counter(), freq);
}

bool sddf_uacpi_init(sddf_uacpi_init_args_t *init_args)
{
    heap = tlsf_create_with_pool(acpi_heap, ACPI_HEAP_SIZE);
    if (!heap) {
        DEBUG_ACPI_ERR("Failed to initialise heap\n");
        return false;
    }

    memcpy(rsdp_buf, init_args->rsdp_blob, sizeof(struct acpi_rsdp));
    post_capdl_shadow_cnode = init_args->post_capdl_shadow_cnode;
    vspace_cptr = init_args->vspace_cptr;

    size_t x86_ioport_ctrl_cslot;
    if (!shadow_cnode_find_cap_slot_of_type(post_capdl_shadow_cnode, CAP_TYPE_X86_IO_PORT_CONTROL,
                                            &x86_ioport_ctrl_cslot)) {
        DEBUG_ACPI_ERR("capDL initialiser did not grant I/O Port control cap\n");
        return false;
    }
    x86_ioport_ctrl_cptr = shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, x86_ioport_ctrl_cslot);

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

    DEBUG_ACPI("Mapping ECAM(s) for firmware specific PCI initialisation\n");
    uacpi_table mcfg_handle;
    if (uacpi_table_find_by_signature(ACPI_MCFG_SIGNATURE, &mcfg_handle) != UACPI_STATUS_OK) {
        DEBUG_ACPI("Firmware did not provide MCFG, falling back to legacy PIO\n");
        assert(false); // @billn TODO
    } else {
        struct acpi_mcfg *mcfg = mcfg_handle.ptr;
        uint64_t mcfg_size = mcfg_handle.hdr->length;
        int mcfg_table_size = mcfg_size - sizeof(uint64_t) - sizeof(struct acpi_sdt_hdr);
        assert(mcfg_table_size % sizeof(struct acpi_mcfg_allocation) == 0);
        int num_mcfg_entries = mcfg_table_size / sizeof(struct acpi_mcfg_allocation);
        for (int i = 0; i < num_mcfg_entries; i++) {
            struct acpi_mcfg_allocation *entry = &mcfg->entries[i];
            DEBUG_ACPI("MCFG entry %d: paddr 0x%lx, segment %u, bus %u..%u\n", i, entry->address, entry->segment,
                       entry->start_bus, entry->end_bus);

            if (i >= MAX_NUM_ECAM) {
                DEBUG_ACPI_ERR("Not recording this ECAM\n");
                continue;
            }

            ecams[num_ecams].start_bus = entry->start_bus;
            ecams[num_ecams].end_bus = entry->end_bus;
            ecams[num_ecams].segment = entry->segment;

            /* Quirk: base address is for bus 0 of that segment, so if the start bus isn't zero
             * we need to account for that.
             * Each bus takes 1 MiB of ECAM space (32 devices × 8 functions × 4 KiB) */
            uint64_t paddr_base = entry->address + ((uint64_t)entry->start_bus << 20);
            size_t size_bytes = ((uint64_t)(entry->end_bus - entry->start_bus) + 1) << 20;

            /* ECAM tends to be quite large so lets just use 2MiB page to avoid running out of room
             * in our small CNode. */
            size_bytes = ROUND_UP(size_bytes, BIT(seL4_LargePageBits));

            ecams[num_ecams].size_bytes = size_bytes;

            uint64_t ecam_vaddr = next_avail_ecam_vaddr;
            if (ecam_vaddr + size_bytes > MAX_ECAM_VADDR) {
                DEBUG_ACPI_ERR("Not enough vaddr range for ECAM %d\n", i);
                return false;
            }

            if (!map_memory_region(post_capdl_shadow_cnode, vspace_cptr, paddr_base, size_bytes, true, ecam_vaddr,
                                   seL4_ReadWrite, seL4_X86_CacheDisabled)) {
                DEBUG_ACPI_ERR("can't map ECAM %d at vaddr 0x%lx\n", i, ecam_vaddr);
                return false;
            }

            ecams[num_ecams].vaddr = (void *)ecam_vaddr;
            num_ecams++;
            next_avail_ecam_vaddr += size_bytes;
        }
        assert(uacpi_table_unref(&mcfg_handle) == UACPI_STATUS_OK);
    }

    DEBUG_ACPI("Executing DSDT and SSDTs...\n");
    status = uacpi_namespace_load();
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to parse and execute all DSDT and SSDT tables, error '%s'\n",
                       uacpi_status_to_string(status));
        return false;
    }
    DEBUG_ACPI("DSDT and SSDTs executed\n");

    DEBUG_ACPI("Setting interrupt model to I/O APIC...\n");
    status = uacpi_set_interrupt_model(UACPI_INTERRUPT_MODEL_IOAPIC);
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to set interrupt model to I/O APIC, error '%s'\n", uacpi_status_to_string(status));
        return false;
    }
    DEBUG_ACPI("Interrupt model set to I/O APIC\n");

    return true;
}

bool sddf_uacpi_retrieve_pci_resources(void)
{
    return false;
}

bool sddf_uacpi_teardown(void)
{
    memset(acpi_heap, 0, sizeof(acpi_heap));
    memset(heap, 0, sizeof(heap));
    memset(paddr_mapped, 0, sizeof(paddr_mapped));
    num_p_mapped = 0;
    memset(rsdp_buf, 0, sizeof(rsdp_buf));
    memset(ecams, 0, sizeof(ecams));
    num_ecams = 0;

    size_t num_slots;
    shadow_cap_t *caps = shadow_cnode_get_caps_table(post_capdl_shadow_cnode, &num_slots);
    size_t num_io_port_caps_deleted = 0;
    for (size_t io_port_cslot = 0; io_port_cslot < num_slots; io_port_cslot++) {
        if (caps[io_port_cslot].type == CAP_TYPE_X86_IO_PORT) {
            assert(seL4_CNode_Delete(shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, 0), io_port_cslot, 58)
                   == seL4_NoError);
            num_io_port_caps_deleted++;
        }
    }

    DEBUG_ACPI("Deleted %lu I/O Port caps\n", num_io_port_caps_deleted);

    return true;
}