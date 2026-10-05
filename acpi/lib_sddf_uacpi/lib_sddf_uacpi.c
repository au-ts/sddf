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
#include <uacpi/context.h>
#include <uacpi/utilities.h>
#include <sddf/acpi/lib_sddf_uacpi.h>
#include <sddf/util/arch_timestamp_counter.h>
#include <sddf/util/printf.h>
#include <sddf/util/vspace.h>
#include <sddf/util/shadow_cnode.h>
#include <sddf/util/tlsf/tlsf.h>
#include <sddf/timer/timer_common.h>
#include "logging.h"
#include "types.h"

alignas(8) lib_sddf_uacpi_state_t lib_state;

uacpi_status uacpi_kernel_get_rsdp(uacpi_phys_addr *out_rsdp_address)
{
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
        return &lib_state.rsdp_buf;
    }

    uint64_t cur_paddr = ROUND_DOWN(addr, PAGE_SIZE_4K);
    uint64_t target_paddr_end = ROUND_UP(addr + len, PAGE_SIZE_4K);

    while (cur_paddr < target_paddr_end) {
        int i = 0;
        bool mapped = false;
        while (i < lib_state.num_p_mapped) {
            if (lib_state.paddr_mapped[i] == cur_paddr) {
                mapped = true;
                break;
            }
            i++;
        }

        if (!mapped) {
            if (lib_state.num_p_mapped == MAX_PADDR_MAPPED) {
                DEBUG_ACPI_ERR("ran out of bookkeeping\n");
                return NULL;
            }

            if (map_memory_region(lib_state.post_capdl_shadow_cnode, lib_state.vspace_cptr, cur_paddr, PAGE_SIZE_4K,
                                  false, ACPI_DIRECT_MAP_BASE + cur_paddr, seL4_ReadWrite, seL4_X86_CacheDisabled)) {
                lib_state.paddr_mapped[lib_state.num_p_mapped] = cur_paddr;
                lib_state.num_p_mapped++;
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
    void *p = tlsf_malloc(lib_state.acpi_heap, size);
    if (!p) {
        DEBUG_ACPI_ERR("out of heap memory, consider increasing ACPI_HEAP_SIZE\n");
    }
    return p;
}

void uacpi_kernel_free(void *mem)
{
    tlsf_free(lib_state.acpi_heap, mem);
}

uacpi_status uacpi_kernel_pci_device_open(uacpi_pci_address address, uacpi_handle *out_handle)
{
    // @billn handle when firmware did not provide mcfg
    int ecam_idx = 0;
    for (; ecam_idx < lib_state.num_ecams; ecam_idx++) {
        if (address.segment == lib_state.ecams[ecam_idx].segment && address.bus >= lib_state.ecams[ecam_idx].start_bus
            && address.bus <= lib_state.ecams[ecam_idx].end_bus) {
            break;
        }
    }

    if (ecam_idx == lib_state.num_ecams) {
        DEBUG_ACPI_ERR("failed to find matching ECAM for %u:%u.%u in PCI segment %u\n", address.bus, address.device,
                       address.function, address.segment);
        return UACPI_STATUS_NOT_FOUND;
    }

    void *config_space_vaddr = (void *)((uintptr_t)(lib_state.ecams[ecam_idx].vaddr)
                                        + ((uint64_t)(address.bus - lib_state.ecams[ecam_idx].start_bus) << 20
                                           | (uint64_t)address.device << 15 | (uint64_t)address.function << 12));

    pci_device_uacpi_handle_t *handle = tlsf_malloc(lib_state.acpi_heap, sizeof(pci_device_uacpi_handle_t));
    if (!handle) {
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    handle->config_space_vaddr = config_space_vaddr;
    *out_handle = handle;

    return UACPI_STATUS_OK;
}

void uacpi_kernel_pci_device_close(uacpi_handle handle)
{
    tlsf_free(lib_state.acpi_heap, handle);
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

bool sddf_uacpi_init(sddf_uacpi_init_args_t *init_args)
{
    memset(&lib_state, 0, sizeof(lib_state));

    lib_state.acpi_heap = tlsf_create_with_pool(lib_state.acpi_heap_buf, ACPI_HEAP_SIZE);
    if (!lib_state.acpi_heap) {
        DEBUG_ACPI_ERR("Failed to initialise heap\n");
        return false;
    }

    lib_state.vspace_cptr = init_args->vspace_cptr;
    lib_state.next_avail_ecam_vaddr = BIT(27);

    memcpy(lib_state.rsdp_buf, init_args->rsdp_blob, sizeof(struct acpi_rsdp));
    lib_state.post_capdl_shadow_cnode = init_args->post_capdl_shadow_cnode;

    size_t x86_ioport_ctrl_cslot;
    if (!shadow_cnode_find_cap_slot_of_type(lib_state.post_capdl_shadow_cnode, CAP_TYPE_X86_IO_PORT_CONTROL,
                                            &x86_ioport_ctrl_cslot)) {
        DEBUG_ACPI_ERR("capDL initialiser did not grant I/O Port control cap\n");
        return false;
    }
    lib_state.x86_ioport_ctrl_cptr = shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode,
                                                                x86_ioport_ctrl_cslot);

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
        size_t mcfg_table_size = mcfg_size - sizeof(uint64_t) - sizeof(struct acpi_sdt_hdr);
        if (mcfg_table_size % sizeof(struct acpi_mcfg_allocation) != 0) {
            DEBUG_ACPI_ERR("mcfg_table_size 0x%lx is not a multiple of sizeof(struct acpi_mcfg_allocation) 0x%lx\n",
                           mcfg_table_size, sizeof(struct acpi_mcfg_allocation));
            return false;
        }
        int num_mcfg_entries = mcfg_table_size / sizeof(struct acpi_mcfg_allocation);
        for (int i = 0; i < num_mcfg_entries; i++) {
            struct acpi_mcfg_allocation *entry = &mcfg->entries[i];
            DEBUG_ACPI("MCFG entry %d: paddr 0x%lx, segment %u, bus %u..%u\n", i, entry->address, entry->segment,
                       entry->start_bus, entry->end_bus);

            if (i >= MAX_NUM_ECAM) {
                DEBUG_ACPI_ERR("Not recording this ECAM\n");
                continue;
            }

            lib_state.ecams[lib_state.num_ecams].paddr = entry->address;
            lib_state.ecams[lib_state.num_ecams].start_bus = entry->start_bus;
            lib_state.ecams[lib_state.num_ecams].end_bus = entry->end_bus;
            lib_state.ecams[lib_state.num_ecams].segment = entry->segment;

            /* Quirk: base address is for bus 0 of that segment, so if the start bus isn't zero
             * we need to account for that.
             * Each bus takes 1 MiB of ECAM space (32 devices × 8 functions × 4 KiB) */
            uint64_t ecam_start = entry->address + ((uint64_t)entry->start_bus << 20);
            uint64_t ecam_end = entry->address + (((uint64_t)entry->end_bus + 1) << 20);
            uint64_t map_base = ROUND_DOWN(ecam_start, BIT(seL4_LargePageBits));
            size_t map_size = ROUND_UP(ecam_end, BIT(seL4_LargePageBits)) - map_base;

            lib_state.ecams[lib_state.num_ecams].size_bytes = ecam_end - ecam_start;

            uint64_t ecam_vaddr = lib_state.next_avail_ecam_vaddr;
            if (ecam_vaddr + map_size > MAX_ECAM_VADDR) {
                DEBUG_ACPI_ERR("Not enough vaddr range for ECAM %d\n", i);
                return false;
            }

            if (!map_memory_region(lib_state.post_capdl_shadow_cnode, lib_state.vspace_cptr, map_base, map_size, true,
                                   ecam_vaddr, seL4_ReadWrite, seL4_X86_CacheDisabled)) {
                DEBUG_ACPI_ERR("can't map ECAM %d at vaddr 0x%lx\n", i, ecam_vaddr);
                return false;
            }

            lib_state.ecams[lib_state.num_ecams].vaddr = (void *)(ecam_vaddr + (ecam_start - map_base));
            lib_state.num_ecams++;
            lib_state.next_avail_ecam_vaddr += map_size;
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

    DEBUG_ACPI("Initialising namespaces...\n");
    assert(uacpi_namespace_initialize() == UACPI_STATUS_OK);

    DEBUG_ACPI("Namespace initialised\n");
    return true;
}

bool sddf_uacpi_retrieve_pci_resources(void)
{
    return false;
}

bool sddf_uacpi_teardown(void)
{
    // No need to call uacpi_state_reset() because we tear everything down
    // anyways.

    size_t num_slots;
    shadow_cap_t *caps = shadow_cnode_get_caps_table(lib_state.post_capdl_shadow_cnode, &num_slots);
    size_t num_io_port_caps_deleted = 0;
    for (size_t io_port_cslot = 0; io_port_cslot < num_slots; io_port_cslot++) {
        if (caps[io_port_cslot].type == CAP_TYPE_X86_IO_PORT) {
            assert(
                seL4_CNode_Delete(shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, 0), io_port_cslot, 58)
                == seL4_NoError);
            assert(shadow_cnode_delete_cap_at_slot(lib_state.post_capdl_shadow_cnode, io_port_cslot));
            num_io_port_caps_deleted++;
        }
    }

    // todo, need to pass og capdl ut range in init, then loop n revoke

    DEBUG_ACPI("Deleted %lu I/O Port caps\n", num_io_port_caps_deleted);

    memset(&lib_state, 0, sizeof(lib_state));
    return true;
}