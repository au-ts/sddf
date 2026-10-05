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
#include "../logging.h"
#include "../types.h"

#define IOAPIC_LEVEL_TRIGGER 1
#define IOAPIC_EDGE_TRIGGER 0
#define IOAPIC_ACTIVE_LOW 1
#define IOAPIC_ACTIVE_HIGH 0

extern lib_sddf_uacpi_state_t lib_state;

static void delay_for_ns(uint64_t ns)
{
    uint64_t freq = sddf_read_freq();
    if (!freq) {
        DEBUG_ACPI_ERR("TSC frequency unavailable\n");
        return;
    }

    uint64_t curr_ns = ticks_to_ns(sddf_read_counter(), freq);
    uint64_t target_ns = curr_ns + ns;
    while (curr_ns < target_ns) {
        seL4_Yield();
        curr_ns = ticks_to_ns(sddf_read_counter(), freq);
    };
}

static void irq_poll(void)
{
    if (lib_state.sci_handle) {
        seL4_Word badge = 0;
        seL4_Poll(shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, lib_state.sci_handle->ntfn_cslot),
                  &badge);

        if (badge) {
            DEBUG_ACPI("irq received\n");
            lib_state.sci_handle->uacpi_callback(lib_state.sci_handle->uacpi_ctx);
            seL4_IRQHandler_Ack(
                shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, lib_state.sci_handle->irq_cslot));
        }
    }
}

uacpi_u64 uacpi_kernel_get_nanoseconds_since_boot(void)
{
    uint64_t freq = sddf_read_freq();
    if (!freq) {
        DEBUG_ACPI_ERR("TSC frequency unavailable\n");
        // @billn a bit dodgy
        return sddf_read_counter();
    }
    return ticks_to_ns(sddf_read_counter(), freq);
}

void uacpi_kernel_stall(uacpi_u8 usec)
{
    delay_for_ns((uint64_t)usec * NS_IN_US);
    irq_poll();
}

void uacpi_kernel_sleep(uacpi_u64 msec)
{
    delay_for_ns((uint64_t)msec * NS_IN_MS);
    irq_poll();
}

uacpi_handle uacpi_kernel_create_event(void)
{
    uint64_t *ev = tlsf_malloc(lib_state.acpi_heap, sizeof(uint64_t));
    if (ev) {
        *ev = 0;
    }
    return ev;
}

void uacpi_kernel_free_event(uacpi_handle handle)
{
    tlsf_free(lib_state.acpi_heap, handle);
}

uacpi_bool uacpi_kernel_wait_for_event(uacpi_handle handle, uacpi_u16 timeout)
{
    uint64_t *ev = handle;
    uint64_t now = uacpi_kernel_get_nanoseconds_since_boot();
    uint64_t deadline = (timeout == 0xFFFF) ? UINT64_MAX : now + (uint64_t)timeout * NS_IN_MS;

    for (;;) {
        irq_poll();
        if (*ev) {
            (*ev)--;
            return UACPI_TRUE;
        }
        if (uacpi_kernel_get_nanoseconds_since_boot() >= deadline) {
            return UACPI_FALSE;
        }
        seL4_Yield();
    }
}

void uacpi_kernel_signal_event(uacpi_handle handle)
{
    *((uint64_t *)handle) += 1;
}

void uacpi_kernel_reset_event(uacpi_handle handle)
{
    *((uint64_t *)handle) = 0;
}

/* Currently assumes a single SCI, so calling this multiple time will fail. */
uacpi_status uacpi_kernel_install_interrupt_handler(uacpi_u32 irq, uacpi_interrupt_handler irq_handle, uacpi_handle ctx,
                                                    uacpi_handle *out_irq_handle)
{
    if (lib_state.sci_handle) {
        DEBUG_ACPI_ERR("SCI already installed\n");
        return UACPI_STATUS_ALREADY_EXISTS;
    }

    DEBUG_ACPI("attempting to install GSI %u\n", irq);

    /* Gotta map the Global System Interrupt to what I/O APIC chip and pin it is wired to. */

    uacpi_table madt_handle;
    if (uacpi_table_find_by_signature(ACPI_MADT_SIGNATURE, &madt_handle) != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("cannot find MADT to map GSI to I/O APIC chip and pin!\n");
        return UACPI_STATUS_DENIED;
    }

    size_t irq_control_cslot;
    if (!shadow_cnode_find_cap_slot_of_type(lib_state.post_capdl_shadow_cnode, CAP_TYPE_IRQ_CONTROL,
                                            &irq_control_cslot)) {
        DEBUG_ACPI_ERR("cannot find IRQ control cap in shadow CNode\n");
        return UACPI_STATUS_DENIED;
    }
    seL4_CPtr irq_ctrl_cptr = shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, irq_control_cslot);

    size_t new_irq_cslot;
    if (!shadow_cnode_find_free_slot(lib_state.post_capdl_shadow_cnode, &new_irq_cslot)) {
        DEBUG_ACPI_ERR("no space in CNode\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    /* The MADT table have variable sized entries...
     * First scan, find if the motherboard have any quirks relating to this GSI specifically */
    seL4_Word level = IOAPIC_LEVEL_TRIGGER;
    seL4_Word polarity = IOAPIC_ACTIVE_LOW;
    seL4_Word vector = 1;

    struct acpi_madt *madt = madt_handle.ptr;
    size_t cur_madt_offset = offsetof(struct acpi_madt, entries);
    while (cur_madt_offset < madt->hdr.length) {
        size_t cur_entry_vaddr = madt_handle.virt_addr + cur_madt_offset;
        struct acpi_entry_hdr *cur_entry_hdr = (struct acpi_entry_hdr *)cur_entry_vaddr;
        if (cur_entry_hdr->type == ACPI_MADT_ENTRY_TYPE_INTERRUPT_SOURCE_OVERRIDE) {
            if (cur_entry_hdr->length != sizeof(struct acpi_madt_interrupt_source_override)) {
                DEBUG_ACPI_ERR("found an ISO entry with a bad length %u != %zu, skipping!\n", cur_entry_hdr->length,
                               sizeof(struct acpi_madt_interrupt_source_override));
                goto skip_entry_1;
            }

            struct acpi_madt_interrupt_source_override iso_entry;
            memcpy(&iso_entry, cur_entry_hdr, sizeof(iso_entry));

            DEBUG_ACPI("found ISO bus %u, source %u, GSI %u, flags 0x%x\n", iso_entry.bus, iso_entry.source,
                       iso_entry.gsi, iso_entry.flags);

            if (irq == iso_entry.gsi && iso_entry.flags) {
                DEBUG_ACPI("SCI is quirky, applying quirks\n");

                if ((iso_entry.flags & ACPI_MADT_TRIGGERING_MASK) != ACPI_MADT_TRIGGERING_CONFORMING) {
                    level = (iso_entry.flags & ACPI_MADT_TRIGGERING_LEVEL) == ACPI_MADT_TRIGGERING_LEVEL
                              ? IOAPIC_LEVEL_TRIGGER
                              : IOAPIC_EDGE_TRIGGER;
                }

                if ((iso_entry.flags & ACPI_MADT_POLARITY_MASK) != ACPI_MADT_POLARITY_CONFORMING) {
                    polarity = (iso_entry.flags & ACPI_MADT_POLARITY_ACTIVE_LOW) == ACPI_MADT_POLARITY_ACTIVE_LOW
                                 ? IOAPIC_ACTIVE_LOW
                                 : IOAPIC_ACTIVE_HIGH;
                }
            }
        }

    skip_entry_1:
        cur_madt_offset += cur_entry_hdr->length;
    }

    size_t ioapic_sequence = 0;
    bool irq_cap_created = false;
    cur_madt_offset = offsetof(struct acpi_madt, entries);
    while (cur_madt_offset < madt->hdr.length) {
        size_t cur_entry_vaddr = madt_handle.virt_addr + cur_madt_offset;
        struct acpi_entry_hdr *cur_entry_hdr = (struct acpi_entry_hdr *)cur_entry_vaddr;
        if (cur_entry_hdr->type == ACPI_MADT_ENTRY_TYPE_IOAPIC) {
            if (cur_entry_hdr->length != sizeof(struct acpi_madt_ioapic)) {
                DEBUG_ACPI_ERR("found an I/O APIC entry with a bad length %u != %zu, skipping!\n",
                               cur_entry_hdr->length, sizeof(struct acpi_madt_ioapic));
                goto skip_entry_2;
            }

            struct acpi_madt_ioapic ioapic_entry;
            memcpy(&ioapic_entry, cur_entry_hdr, sizeof(ioapic_entry));

            DEBUG_ACPI("found IOAPIC id %u, sequence %zu, GSI base %u\n", ioapic_entry.id, ioapic_sequence,
                       ioapic_entry.gsi_base);

            if (irq < ioapic_entry.gsi_base) {
                ioapic_sequence++;
                goto skip_entry_2;
            }
            size_t pin_maybe = irq - ioapic_entry.gsi_base;

            /* There is no way to query how many pins that the I/O APIC actually support, since that information
             * is from the I/O APIC register, and seL4 doesn't expose this information, nor allow you to map the
             * registers (this would be dangerous anyways). So we just trial and error: */

            if (seL4_IRQControl_GetIOAPIC(irq_ctrl_cptr,
                                          shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, 0),
                                          new_irq_cslot, 58, ioapic_sequence, pin_maybe, level, polarity, vector)
                == seL4_NoError) {

                assert(shadow_cnode_insert_cap_at_slot(lib_state.post_capdl_shadow_cnode,
                                                       &SHADOW_CNODE_MAKE_CAP(CAP_TYPE_IRQ, 0, 0, 0, 0),
                                                       new_irq_cslot));
                DEBUG_ACPI("IRQ cap created at this IOAPIC\n");
                irq_cap_created = true;
                break;
            }

            ioapic_sequence++;
        }

    skip_entry_2:
        cur_madt_offset += cur_entry_hdr->length;
    }

    if (uacpi_table_unref(&madt_handle) != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("failed to free MADT handle\n");
        return UACPI_STATUS_DENIED;
    }

    if (!irq_cap_created) {
        DEBUG_ACPI_ERR("failed to create IRQ cap\n");
        return UACPI_STATUS_DENIED;
    }

    size_t new_nftn_cslot;
    if (!shadow_cnode_retype(lib_state.post_capdl_shadow_cnode, seL4_NotificationObject, 0, &new_nftn_cslot)) {
        DEBUG_ACPI_ERR("Failed to create notification object\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    size_t badged_nftn_cslot;
    if (!shadow_cnode_find_free_slot(lib_state.post_capdl_shadow_cnode, &badged_nftn_cslot)) {
        DEBUG_ACPI_ERR("no space in CNode\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    if (seL4_CNode_Mint(shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, 0), badged_nftn_cslot, 58,
                        shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, 0), new_nftn_cslot, 58,
                        seL4_ReadWrite, 1)
        != seL4_NoError) {
        DEBUG_ACPI_ERR("can't mint ntfn with badge\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    assert(shadow_cnode_insert_cap_at_slot(lib_state.post_capdl_shadow_cnode,
                                           &SHADOW_CNODE_MAKE_CAP(CAP_TYPE_NTFN, 0, 0, 0, 0), badged_nftn_cslot));

    seL4_CPtr irq_cptr = shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, new_irq_cslot);
    seL4_CPtr ntfn_cptr = shadow_cnode_cslot_to_cptr(lib_state.post_capdl_shadow_cnode, badged_nftn_cslot);
    if (seL4_IRQHandler_SetNotification(irq_cptr, ntfn_cptr) != seL4_NoError) {
        DEBUG_ACPI_ERR("Failed to bind IRQ to notification\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    if (seL4_IRQHandler_Ack(irq_cptr) != seL4_NoError) {
        DEBUG_ACPI_ERR("Failed to ack IRQ\n");
        return UACPI_STATUS_DENIED;
    }

    irq_handle_t *handle = tlsf_malloc(lib_state.acpi_heap, sizeof(irq_handle_t));
    if (!handle) {
        DEBUG_ACPI_ERR("out of memory\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    handle->irq_cslot = new_irq_cslot;
    handle->ntfn_cslot = badged_nftn_cslot;
    handle->uacpi_callback = irq_handle;
    handle->uacpi_ctx = ctx;

    DEBUG_ACPI("IRQHandler cap at CSlot %zu created for GSI %u, badged notification CSlot %zu\n", new_irq_cslot, irq,
               badged_nftn_cslot);

    *out_irq_handle = handle;
    lib_state.sci_handle = handle;

    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_uninstall_interrupt_handler(uacpi_interrupt_handler handle, uacpi_handle irq_handle)
{
    // @billn todo
    return UACPI_STATUS_OK;
}