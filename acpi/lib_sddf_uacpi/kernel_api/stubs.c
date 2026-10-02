/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include "../logging.h"

/* This file contains all the OS functions uACPI expects but we have not implemented or the
 * implementation is very minimal. To reduce clutter in lib_sddf_uacpi.c */

void uacpi_kernel_unmap(void *addr, uacpi_size len)
{
    /* no-op */
}

/* Stubs for mutex and spinlock, this is sound as Microkit PDs are single threaded */
static uint64_t dummy_mutex = 0;
static uint64_t dummy_spinlock = 0;

uacpi_handle uacpi_kernel_create_mutex(void)
{
    dummy_mutex++;
    return (uacpi_handle)dummy_mutex;
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
    return (uacpi_thread_id)1;
}

uacpi_handle uacpi_kernel_create_spinlock(void)
{
    dummy_spinlock++;
    return (uacpi_handle)dummy_spinlock;
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

uacpi_interrupt_state uacpi_kernel_disable_interrupts(void)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
    return 0;
}

void uacpi_kernel_restore_interrupts(uacpi_interrupt_state state)
{
    DEBUG_ACPI(COLOUR_RED "unimplemented" COLOUR_RESET "\n");
}

uacpi_status uacpi_kernel_handle_firmware_request(uacpi_firmware_request *firmware_req)
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
