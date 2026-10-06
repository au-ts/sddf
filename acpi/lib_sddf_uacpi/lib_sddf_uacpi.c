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

bool sddf_uacpi_init(sddf_uacpi_init_args_t *init_args)
{
    DEBUG_ACPI("Initialising uACPI...\n");
    memset(&lib_state, 0, sizeof(lib_state));
    lib_state.post_capdl_shadow_cnode = init_args->post_capdl_shadow_cnode;

    lib_state.acpi_heap = tlsf_create_with_pool(lib_state.acpi_heap_buf, ACPI_HEAP_SIZE);
    if (!lib_state.acpi_heap) {
        DEBUG_ACPI_ERR("Failed to initialise heap\n");
        return false;
    }

    lib_state.cnode_cptr = shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, 0);
    lib_state.vspace_cptr = init_args->vspace_cptr;

    memcpy(lib_state.rsdp_buf, init_args->rsdp_blob, sizeof(struct acpi_rsdp));

    size_t x86_ioport_ctrl_cslot;
    if (!shadow_cnode_find_cap_slot_of_type(lib_state.post_capdl_shadow_cnode, CAP_TYPE_X86_IO_PORT_CONTROL,
                                            &x86_ioport_ctrl_cslot)) {
        DEBUG_ACPI_ERR("capDL initialiser did not grant I/O Port control cap\n");
        return false;
    }
    seL4_CPtr x86_ioport_ctrl_cptr = shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode,
                                                                x86_ioport_ctrl_cslot);

    size_t x86_ioport_master_cslot;
    if (!shadow_cnode_find_free_slot(lib_state.post_capdl_shadow_cnode, &x86_ioport_master_cslot)) {
        DEBUG_ACPI_ERR("out of CSlot\n");
        return false;
    }

    if (seL4_X86_IOPortControl_Issue(x86_ioport_ctrl_cptr, 0, UINT16_MAX, lib_state.cnode_cptr, x86_ioport_master_cslot,
                                     58)
        != seL4_NoError) {
        DEBUG_ACPI_ERR("can't create io port master cap.\n");
        return false;
    }

    assert(shadow_cnode_insert_cap_at_slot(
        lib_state.post_capdl_shadow_cnode,
        &SHADOW_CNODE_MAKE_CAP(CAP_TYPE_X86_IO_PORT, 0, UINT16_MAX, x86_ioport_ctrl_cslot, 0),
        x86_ioport_master_cslot));

    lib_state.x86_ioport_master_cslot = x86_ioport_master_cslot;

    /* Default settings for uACPI: enter ACPI mode on the platform, and don't error out if a table
     * checksum is bad in case the firmware have a bug. */
    uint64_t flags = 0;
    uacpi_status status = uacpi_initialize(flags);
    if (status != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("Failed to initialise uACPI, error '%s'\n", uacpi_status_to_string(status));
        return false;
    }
    DEBUG_ACPI("uACPI initialised\n");

    DEBUG_ACPI("Enumerating ECAM(s) for firmware specific PCI initialisation\n");
    uacpi_table mcfg_handle;
    if (uacpi_table_find_by_signature(ACPI_MCFG_SIGNATURE, &mcfg_handle) != UACPI_STATUS_OK) {
        DEBUG_ACPI("Firmware did not provide MCFG, falling back to legacy PIO for PCI access\n");
        assert(false); // @billn actually implement
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
            lib_state.num_ecams++;
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
    uacpi_state_reset();

    size_t num_slots;
    shadow_cap_t *caps = shadow_cnode_get_caps_table(lib_state.post_capdl_shadow_cnode, &num_slots);
    size_t num_io_port_caps_deleted = 0;
    size_t num_irq_caps_deleted = 0;
    size_t num_ut_caps_revoked = 0;
    size_t num_ut_caps_deleted = 0;

    for (size_t cslot = 0; cslot < num_slots; cslot++) {
        if (caps[cslot].type == CAP_TYPE_X86_IO_PORT) {
            assert(seL4_CNode_Delete(lib_state.cnode_cptr, cslot, 58) == seL4_NoError);
            assert(shadow_cnode_delete_cap_at_slot(lib_state.post_capdl_shadow_cnode, cslot));
            num_io_port_caps_deleted++;
        } else if (caps[cslot].type == CAP_TYPE_IRQ) {
            assert(seL4_CNode_Delete(lib_state.cnode_cptr, cslot, 58) == seL4_NoError);
            assert(shadow_cnode_delete_cap_at_slot(lib_state.post_capdl_shadow_cnode, cslot));
            num_irq_caps_deleted++;
        } else if (caps[cslot].type == CAP_TYPE_UT) {
            if (caps[cslot].parent_cslot == PARENT_CSLOT_NONE) {
                assert(seL4_CNode_Revoke(lib_state.cnode_cptr, cslot, 58) == seL4_NoError);
                num_ut_caps_revoked++;
            } else {
                num_ut_caps_deleted++;
            }
            assert(shadow_cnode_delete_cap_at_slot(lib_state.post_capdl_shadow_cnode, cslot));
        }
    }

    DEBUG_ACPI("Deleted %lu I/O Port caps\n", num_io_port_caps_deleted);
    DEBUG_ACPI("Deleted %lu IRQ caps\n", num_irq_caps_deleted);
    DEBUG_ACPI("Revoked %lu UT caps, which resulted in deleting %lu child UT caps\n", num_ut_caps_revoked,
               num_ut_caps_deleted);

    // @billn todo, reset the shadow cnode into original state.

    memset(&lib_state, 0, sizeof(lib_state));
    return true;
}