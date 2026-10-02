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

    if (ecam_idx == num_ecams) {
        DEBUG_ACPI_ERR("failed to find matching ECAM for %u:%u.%u in PCI segment %u\n", address.bus, address.device,
                       address.function, address.segment);
        return UACPI_STATUS_NOT_FOUND;
    }

    void *config_space_vaddr = (void *)((uintptr_t)(ecams[ecam_idx].vaddr)
                                        + ((uint64_t)(address.bus - ecams[ecam_idx].start_bus) << 20
                                           | (uint64_t)address.device << 15 | (uint64_t)address.function << 12));

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
        DEBUG_ACPI_ERR("TSC frequency unavailable\n");
        // @billn a bit dodgy
        return sddf_read_counter();
    }
    return ticks_to_ns(sddf_read_counter(), freq);
}

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

void uacpi_kernel_stall(uacpi_u8 usec)
{
    delay_for_ns((uint64_t)usec * NS_IN_US);
}

void uacpi_kernel_sleep(uacpi_u64 msec)
{
    delay_for_ns((uint64_t)msec * NS_IN_MS);
}

uacpi_handle uacpi_kernel_create_event(void)
{
    uint64_t *ev = tlsf_malloc(heap, sizeof(uint64_t));
    if (ev) {
        *ev = 0;
    }
    return ev;
}

void uacpi_kernel_free_event(uacpi_handle handle)
{
    tlsf_free(heap, handle);
}

uacpi_bool uacpi_kernel_wait_for_event(uacpi_handle handle, uacpi_u16 timeout)
{
    /* We don't care about the timeout since Microkit PD code are un-preemptible even
     * with a pending IRQ at the bound notification, except by the kernel's scheduler.
     * so if the event isn't ready then just bail. */

    if (*((uint64_t *)handle) > 0) {
        *((uint64_t *)handle) -= 1;
        return UACPI_TRUE;
    }
    return UACPI_FALSE;
}

void uacpi_kernel_signal_event(uacpi_handle handle)
{
    *((uint64_t *)handle) += 1;
}

void uacpi_kernel_reset_event(uacpi_handle handle)
{
    *((uint64_t *)handle) = 0;
}

typedef struct {
    size_t irq_cslot;
    size_t ntfn_cslot;
    uacpi_interrupt_handler uacpi_callback;
    uacpi_handle uacpi_ctx;
} irq_handle_t;

irq_handle_t *sci_handle = NULL;

uacpi_status uacpi_kernel_install_interrupt_handler(uacpi_u32 irq, uacpi_interrupt_handler irq_handle, uacpi_handle ctx,
                                                    uacpi_handle *out_irq_handle)
{
    DEBUG_ACPI("attempting to install GSI %u\n", irq);

    /* Gotta map the Global System Interrupt to what I/O APIC chip and pin it is wired to. */

    uacpi_table madt_handle;
    if (uacpi_table_find_by_signature(ACPI_MADT_SIGNATURE, &madt_handle) != UACPI_STATUS_OK) {
        DEBUG_ACPI_ERR("cannot find MADT to map GSI to I/O APIC chip and pin!\n");
        return UACPI_STATUS_DENIED;
    }

    size_t irq_control_cslot;
    if (!shadow_cnode_find_cap_slot_of_type(post_capdl_shadow_cnode, CAP_TYPE_IRQ_CONTROL, &irq_control_cslot)) {
        DEBUG_ACPI_ERR("cannot find IRQ control cap in shadow CNode\n");
        return UACPI_STATUS_DENIED;
    }
    seL4_CPtr irq_ctrl_cptr = shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, irq_control_cslot);

    size_t new_irq_cslot;
    if (!shadow_cnode_find_free_slot(post_capdl_shadow_cnode, &new_irq_cslot)) {
        DEBUG_ACPI_ERR("no space in CNode\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    size_t ioapic_sequence = 0;
    bool irq_cap_created = false;

    /* The MADT table have variable sized entries... */
    struct acpi_madt *madt = madt_handle.ptr;
    size_t cur_madt_offset = offsetof(struct acpi_madt, entries);
    while (cur_madt_offset < madt->hdr.length) {
        size_t cur_entry_vaddr = madt_handle.virt_addr + cur_madt_offset;
        struct acpi_entry_hdr *cur_entry_hdr = (struct acpi_entry_hdr *)cur_entry_vaddr;
        if (cur_entry_hdr->type == ACPI_MADT_ENTRY_TYPE_IOAPIC) {
            if (cur_entry_hdr->length != sizeof(struct acpi_madt_ioapic)) {
                DEBUG_ACPI_ERR("found an I/O APIC entry with a bad length %u != %zu, skipping!\n",
                               cur_entry_hdr->length, sizeof(struct acpi_madt_ioapic));
                goto skip_entry;
            }

            struct acpi_madt_ioapic ioapic_entry;
            memcpy(&ioapic_entry, cur_entry_hdr, sizeof(ioapic_entry));

            size_t pin_maybe = irq - ioapic_entry.gsi_base;
            DEBUG_ACPI("found IOAPIC id %u, sequence %zu, GSI base %u, pin maybe %zu\n", ioapic_entry.id,
                       ioapic_sequence, ioapic_entry.gsi_base, pin_maybe);

            /* There is no way to query how many pins that the I/O APIC actually support, since that information
             * is from the I/O APIC register, and seL4 doesn't expose this information, nor allow you to map the
             * registers (this would be dangerous anyways). So we just trial and error: */
            if (seL4_IRQControl_GetIOAPIC(irq_ctrl_cptr, shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, 0),
                                          new_irq_cslot, 58, ioapic_sequence, pin_maybe, 1, 1, 0)
                == seL4_NoError) {

                assert(shadow_cnode_insert_cap_at_slot(
                    post_capdl_shadow_cnode, &SHADOW_CNODE_MAKE_CAP(CAP_TYPE_IRQ, 0, 0, 0, 0), new_irq_cslot));
                DEBUG_ACPI("IRQ cap created at this IOAPIC\n");
                irq_cap_created = true;
                break;
            }

            ioapic_sequence++;
        }

    skip_entry:
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
    if (!shadow_cnode_retype(post_capdl_shadow_cnode, seL4_NotificationObject, 0, &new_nftn_cslot)) {
        DEBUG_ACPI_ERR("Failed to create notification object\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    seL4_CPtr irq_cptr = shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, new_irq_cslot);
    seL4_CPtr ntfn_cptr = shadow_cnode_cslot_to_cptr(post_capdl_shadow_cnode, new_nftn_cslot);
    if (seL4_IRQHandler_SetNotification(irq_cptr, ntfn_cptr) != seL4_NoError) {
        DEBUG_ACPI_ERR("Failed to bind IRQ to notification\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    if (seL4_IRQHandler_Ack(irq_cptr) != seL4_NoError) {
        DEBUG_ACPI_ERR("Failed to ack IRQ\n");
        return UACPI_STATUS_DENIED;
    }

    irq_handle_t *handle = tlsf_malloc(heap, sizeof(irq_handle_t));
    if (!handle) {
        DEBUG_ACPI_ERR("out of memory\n");
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    handle->irq_cslot = new_irq_cslot;
    handle->ntfn_cslot = new_nftn_cslot;
    handle->uacpi_callback = irq_handle;
    handle->uacpi_ctx = ctx;

    DEBUG_ACPI("IRQHandler cap at CSlot %zu created for GSI %u, notification CSlot %zu\n", new_irq_cslot, irq,
               new_nftn_cslot);

    *out_irq_handle = handle;

    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_uninstall_interrupt_handler(uacpi_interrupt_handler handle, uacpi_handle irq_handle)
{
    // @billn todo
    return UACPI_STATUS_OK;
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

            ecams[num_ecams].paddr = entry->address;
            ecams[num_ecams].start_bus = entry->start_bus;
            ecams[num_ecams].end_bus = entry->end_bus;
            ecams[num_ecams].segment = entry->segment;

            /* Quirk: base address is for bus 0 of that segment, so if the start bus isn't zero
             * we need to account for that.
             * Each bus takes 1 MiB of ECAM space (32 devices × 8 functions × 4 KiB) */
            uint64_t ecam_start = entry->address + ((uint64_t)entry->start_bus << 20);
            uint64_t ecam_end = entry->address + (((uint64_t)entry->end_bus + 1) << 20);
            uint64_t map_base = ROUND_DOWN(ecam_start, BIT(seL4_LargePageBits));
            size_t map_size = ROUND_UP(ecam_end, BIT(seL4_LargePageBits)) - map_base;

            ecams[num_ecams].size_bytes = ecam_end - ecam_start;

            uint64_t ecam_vaddr = next_avail_ecam_vaddr;
            if (ecam_vaddr + map_size > MAX_ECAM_VADDR) {
                DEBUG_ACPI_ERR("Not enough vaddr range for ECAM %d\n", i);
                return false;
            }

            if (!map_memory_region(post_capdl_shadow_cnode, vspace_cptr, map_base, map_size, true, ecam_vaddr,
                                   seL4_ReadWrite, seL4_X86_CacheDisabled)) {
                DEBUG_ACPI_ERR("can't map ECAM %d at vaddr 0x%lx\n", i, ecam_vaddr);
                return false;
            }

            ecams[num_ecams].vaddr = (void *)(ecam_vaddr + (ecam_start - map_base));
            num_ecams++;
            next_avail_ecam_vaddr += map_size;
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

    // assert(uacpi_namespace_initialize() == UACPI_STATUS_OK);

    // DEBUG_ACPI("Namespace initialised\n");
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

    memset(acpi_heap, 0, sizeof(acpi_heap));
    heap = NULL;
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
            assert(shadow_cnode_delete_cap_at_slot(post_capdl_shadow_cnode, io_port_cslot));
            num_io_port_caps_deleted++;
        }
    }

    // todo, need to pass og capdl ut range in init, then loop n revoke

    DEBUG_ACPI("Deleted %lu I/O Port caps\n", num_io_port_caps_deleted);

    return true;
}