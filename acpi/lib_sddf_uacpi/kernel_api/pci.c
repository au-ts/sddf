/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <uacpi/uacpi.h>
#include "../logging.h"
#include "../types.h"

extern lib_sddf_uacpi_state_t lib_state;

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

    pci_device_uacpi_handle_t *handle = tlsf_malloc(lib_state.acpi_heap, sizeof(pci_device_uacpi_handle_t));
    if (!handle) {
        return UACPI_STATUS_OUT_OF_MEMORY;
    }

    uint64_t config_space_paddr = lib_state.ecams[ecam_idx].paddr
                                + ((uint64_t)(address.bus) << 20 | (uint64_t)address.device << 15
                                   | (uint64_t)address.function << 12);

    void *config_space_vaddr = uacpi_kernel_map(config_space_paddr, PAGE_SIZE_4K);
    if (!config_space_vaddr) {
        tlsf_free(lib_state.acpi_heap, handle);
        return UACPI_STATUS_DENIED;
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
    if (offset >= PAGE_SIZE_4K) {
        return UACPI_STATUS_INVALID_ARGUMENT;
    }

    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint8_t *reg = (uint8_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *value = *reg;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_read16(uacpi_handle device, uacpi_size offset, uacpi_u16 *value)
{
    if (offset >= PAGE_SIZE_4K) {
        return UACPI_STATUS_INVALID_ARGUMENT;
    }

    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint16_t *reg = (uint16_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *value = *reg;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_read32(uacpi_handle device, uacpi_size offset, uacpi_u32 *value)
{
    if (offset >= PAGE_SIZE_4K) {
        return UACPI_STATUS_INVALID_ARGUMENT;
    }

    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint32_t *reg = (uint32_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *value = *reg;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_write8(uacpi_handle device, uacpi_size offset, uacpi_u8 value)
{
    if (offset >= PAGE_SIZE_4K) {
        return UACPI_STATUS_INVALID_ARGUMENT;
    }

    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint8_t *reg = (uint8_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *reg = value;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_write16(uacpi_handle device, uacpi_size offset, uacpi_u16 value)
{
    if (offset >= PAGE_SIZE_4K) {
        return UACPI_STATUS_INVALID_ARGUMENT;
    }

    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint16_t *reg = (uint16_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *reg = value;
    return UACPI_STATUS_OK;
}

uacpi_status uacpi_kernel_pci_write32(uacpi_handle device, uacpi_size offset, uacpi_u32 value)
{
    if (offset >= PAGE_SIZE_4K) {
        return UACPI_STATUS_INVALID_ARGUMENT;
    }

    pci_device_uacpi_handle_t *handle = (pci_device_uacpi_handle_t *)device;
    volatile uint32_t *reg = (uint32_t *)((uintptr_t)handle->config_space_vaddr + offset);
    *reg = value;
    return UACPI_STATUS_OK;
}
