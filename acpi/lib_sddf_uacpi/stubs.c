/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include "logging.h"

/* This file contains all the OS functions uACPI expects but we have not implemented or the
 * implementation is very minimal. To reduce clutter in lib_sddf_uacpi.c */

void uacpi_kernel_unmap(void *addr, uacpi_size len)
{
    /* no-op */
}

/* Stubs for mutex and spinlock, this is sound as Microkit PDs are single threaded */
static uint8_t mutex;
static uint8_t spinlock;

uacpi_handle uacpi_kernel_create_mutex(void)
{
    return &mutex;
}

void uacpi_kernel_free_mutex(uacpi_handle handle)
{
}

uacpi_status uacpi_kernel_acquire_mutex(uacpi_handle handle, uacpi_u16 timeout)
{
    return UACPI_STATUS_OK;
}

void uacpi_kernel_release_mutex(uacpi_handle handle)
{
}

uacpi_thread_id uacpi_kernel_get_thread_id(void)
{
    return 0;
}

uacpi_handle uacpi_kernel_create_spinlock(void)
{
    return &spinlock;
}

void uacpi_kernel_free_spinlock(uacpi_handle handle)
{
}

uacpi_cpu_flags uacpi_kernel_lock_spinlock(uacpi_handle handle)
{
    return 0;
}

void uacpi_kernel_unlock_spinlock(uacpi_handle handle, uacpi_cpu_flags cpu_flags)
{
}

/* Unimplemented */

uacpi_status uacpi_kernel_pci_device_open(uacpi_pci_address address, uacpi_handle *out_handle)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

void uacpi_kernel_pci_device_close(uacpi_handle handle)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
}

uacpi_status uacpi_kernel_pci_read8(uacpi_handle device, uacpi_size offset, uacpi_u8 *value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_read16(uacpi_handle device, uacpi_size offset, uacpi_u16 *value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_read32(uacpi_handle device, uacpi_size offset, uacpi_u32 *value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_write8(uacpi_handle device, uacpi_size offset, uacpi_u8 value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_write16(uacpi_handle device, uacpi_size offset, uacpi_u16 value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_pci_write32(uacpi_handle device, uacpi_size offset, uacpi_u32 value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_map(uacpi_io_addr base, uacpi_size len, uacpi_handle *out_handle)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

void uacpi_kernel_io_unmap(uacpi_handle handle)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
}

uacpi_status uacpi_kernel_io_read8(uacpi_handle handle, uacpi_size offset, uacpi_u8 *out_value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_read16(uacpi_handle handle, uacpi_size offset, uacpi_u16 *out_value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_read32(uacpi_handle handle, uacpi_size offset, uacpi_u32 *out_value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_write8(uacpi_handle handle, uacpi_size offset, uacpi_u8 in_value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_write16(uacpi_handle handle, uacpi_size offset, uacpi_u16 in_value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_io_write32(uacpi_handle handle, uacpi_size offset, uacpi_u32 in_value)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

void uacpi_kernel_stall(uacpi_u8 usec)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
}

void uacpi_kernel_sleep(uacpi_u64 msec)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
}

uacpi_handle uacpi_kernel_create_event(void)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return NULL;
}

void uacpi_kernel_free_event(uacpi_handle handle)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
}

uacpi_interrupt_state uacpi_kernel_disable_interrupts(void)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return 0;
}

void uacpi_kernel_restore_interrupts(uacpi_interrupt_state state)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
}

uacpi_bool uacpi_kernel_wait_for_event(uacpi_handle handle, uacpi_u16 timeout)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return false;
}

void uacpi_kernel_signal_event(uacpi_handle handle)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
}

void uacpi_kernel_reset_event(uacpi_handle handle)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
}

uacpi_status uacpi_kernel_handle_firmware_request(uacpi_firmware_request *firmware_req)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_install_interrupt_handler(uacpi_u32 irq, uacpi_interrupt_handler irq_handle, uacpi_handle ctx,
                                                    uacpi_handle *out_irq_handle)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_uninstall_interrupt_handler(uacpi_interrupt_handler handle, uacpi_handle irq_handle)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_schedule_work(uacpi_work_type work_type, uacpi_work_handler handle, uacpi_handle ctx)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}

uacpi_status uacpi_kernel_wait_for_work_completion(void)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return UACPI_STATUS_UNIMPLEMENTED;
}
