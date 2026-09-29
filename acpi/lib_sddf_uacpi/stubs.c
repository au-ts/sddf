/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include "logging.h"

/* This file contains all the OS functions uACPI expects but we have not implemented. To reduce
 * clutter in lib_sddf_uacpi.c */

void *uacpi_kernel_map(uacpi_phys_addr addr, uacpi_size len)
{
    DEBUG_ACPI("called\n");
    return NULL;
}

void uacpi_kernel_unmap(void *addr, uacpi_size len)
{
    DEBUG_ACPI("called\n");
}

void uacpi_kernel_log(uacpi_log_level log_level, const uacpi_char *s)
{
    DEBUG_ACPI("%s", s);
}

uacpi_status uacpi_kernel_pci_device_open(uacpi_pci_address address, uacpi_handle *out_handle)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

void uacpi_kernel_pci_device_close(uacpi_handle handle)
{
    DEBUG_ACPI("called\n");
}

uacpi_status uacpi_kernel_pci_read8(uacpi_handle device, uacpi_size offset, uacpi_u8 *value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_read16(uacpi_handle device, uacpi_size offset, uacpi_u16 *value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_read32(uacpi_handle device, uacpi_size offset, uacpi_u32 *value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_write8(uacpi_handle device, uacpi_size offset, uacpi_u8 value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_write16(uacpi_handle device, uacpi_size offset, uacpi_u16 value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_write32(uacpi_handle device, uacpi_size offset, uacpi_u32 value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_map(uacpi_io_addr base, uacpi_size len, uacpi_handle *out_handle)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

void uacpi_kernel_io_unmap(uacpi_handle handle)
{
    DEBUG_ACPI("called\n");
}

uacpi_status uacpi_kernel_io_read8(uacpi_handle handle, uacpi_size offset, uacpi_u8 *out_value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_read16(uacpi_handle handle, uacpi_size offset, uacpi_u16 *out_value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_read32(uacpi_handle handle, uacpi_size offset, uacpi_u32 *out_value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_write8(uacpi_handle handle, uacpi_size offset, uacpi_u8 in_value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_write16(uacpi_handle handle, uacpi_size offset, uacpi_u16 in_value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_write32(uacpi_handle handle, uacpi_size offset, uacpi_u32 in_value)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

void *uacpi_kernel_alloc(uacpi_size size)
{
    DEBUG_ACPI("called\n");
    return NULL;
}

void uacpi_kernel_free(void *mem)
{
    DEBUG_ACPI("called\n");
}

uacpi_u64 uacpi_kernel_get_nanoseconds_since_boot(void)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

void uacpi_kernel_stall(uacpi_u8 usec)
{
    DEBUG_ACPI("called\n");
}

void uacpi_kernel_sleep(uacpi_u64 msec)
{
    DEBUG_ACPI("called\n");
}

uacpi_handle uacpi_kernel_create_mutex(void)
{
    DEBUG_ACPI("called\n");
    return NULL;
}

void uacpi_kernel_free_mutex(uacpi_handle handle)
{
    DEBUG_ACPI("called\n");
}

uacpi_handle uacpi_kernel_create_event(void)
{
    DEBUG_ACPI("called\n");
    return NULL;
}

void uacpi_kernel_free_event(uacpi_handle handle)
{
    DEBUG_ACPI("called\n");
}

uacpi_thread_id uacpi_kernel_get_thread_id(void)
{
    DEBUG_ACPI("called\n");
    return UACPI_THREAD_ID_NONE;
}

uacpi_interrupt_state uacpi_kernel_disable_interrupts(void)
{
    DEBUG_ACPI("called\n");
    return 0;
}

void uacpi_kernel_restore_interrupts(uacpi_interrupt_state state)
{
    DEBUG_ACPI("called\n");
}

uacpi_status uacpi_kernel_acquire_mutex(uacpi_handle handle, uacpi_u16 timeout)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

void uacpi_kernel_release_mutex(uacpi_handle handle)
{
    DEBUG_ACPI("called\n");
}

uacpi_bool uacpi_kernel_wait_for_event(uacpi_handle handle, uacpi_u16 timeout)
{
    DEBUG_ACPI("called\n");
    return false;
}

void uacpi_kernel_signal_event(uacpi_handle handle)
{
    DEBUG_ACPI("called\n");
}

void uacpi_kernel_reset_event(uacpi_handle handle)
{
    DEBUG_ACPI("called\n");
}

uacpi_status uacpi_kernel_handle_firmware_request(uacpi_firmware_request *firmware_req)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_install_interrupt_handler(uacpi_u32 irq, uacpi_interrupt_handler irq_handle, uacpi_handle ctx,
                                                    uacpi_handle *out_irq_handle)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_uninstall_interrupt_handler(uacpi_interrupt_handler handle, uacpi_handle irq_handle)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_handle uacpi_kernel_create_spinlock(void)
{
    DEBUG_ACPI("called\n");

    return NULL;
}

void uacpi_kernel_free_spinlock(uacpi_handle handle)
{
    DEBUG_ACPI("called\n");
}

uacpi_cpu_flags uacpi_kernel_lock_spinlock(uacpi_handle handle)
{
    DEBUG_ACPI("called\n");
    return 0;
}

void uacpi_kernel_unlock_spinlock(uacpi_handle handle, uacpi_cpu_flags cpu_flags)
{
    DEBUG_ACPI("called\n");
}

uacpi_status uacpi_kernel_schedule_work(uacpi_work_type work_type, uacpi_work_handler handle, uacpi_handle ctx)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_wait_for_work_completion(void)
{
    DEBUG_ACPI("called\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}
