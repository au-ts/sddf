/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>

#include <os/sddf.h>
#include <sddf/pcie/protocol.h>

/**
 * Claim the device matching the spec at index `spec_idx` in this client's spec table,
 * as encoded by the metaprogram inside the PCIe driver.
 * The returned handle identifies the device in all other calls to the PCIe driver.
 * @param channel ID of the PCIe driver.
 * @param spec_idx index into this client's spec table.
 * @param handle on success, the handle of the claimed device.
 * @return SDDF_PCIE_STATUS_OK on success,
 *         SDDF_PCIE_STATUS_NOT_FOUND if no device matches the spec,
 *         SDDF_PCIE_STATUS_ALREADY_CLAIMED if the device has already been claimed,
 *         SDDF_PCIE_STATUS_INVALID_ARGUMENT if the spec index is out of bound.
 */
static inline sddf_pcie_status_t sddf_pcie_claim_device(unsigned int channel, uint8_t spec_idx,
                                                        sddf_pcie_handle_t *handle)
{
    sddf_set_mr(0, spec_idx);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_CLAIM_DEVICE, 0, 0, SDDF_PCIE_CLAIM_DEVICE_NUM_WORDS));

    sddf_pcie_status_t status = sddf_get_mr(0);
    if (status == SDDF_PCIE_STATUS_OK) {
        *handle = sddf_get_mr(1);
    }
    return status;
}

/**
 * Read an 8, 16 or 32-bit value from the device's configuration space.
 * To find a BAR's size, use sddf_pcie_get_bar_size() rather than probing the BAR directly.
 * @param channel ID of the PCIe driver.
 * @param handle handle of the claimed device.
 * @param offset byte offset into configuration space, aligned to the access size.
 * @param value on success, the value read.
 * @return SDDF_PCIE_STATUS_OK on success,
 *         SDDF_PCIE_STATUS_INVALID_HANDLE if the handle is invalid,
 *         SDDF_PCIE_STATUS_INVALID_ARGUMENT if the offset is out of range or misaligned.
 *
 */
static inline sddf_pcie_status_t sddf_pcie_read_config_space_8(unsigned int channel, sddf_pcie_handle_t handle,
                                                               uint16_t offset, uint8_t *value)
{
    sddf_set_mr(0, handle);
    sddf_set_mr(1, offset);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_READ_CS_8, 0, 0, SDDF_PCIE_READ_CS_NUM_WORDS));

    sddf_pcie_status_t status = sddf_get_mr(0);
    if (status == SDDF_PCIE_STATUS_OK) {
        *value = sddf_get_mr(1);
    }
    return status;
}

static inline sddf_pcie_status_t sddf_pcie_read_config_space_16(unsigned int channel, sddf_pcie_handle_t handle,
                                                                uint16_t offset, uint16_t *value)
{
    sddf_set_mr(0, handle);
    sddf_set_mr(1, offset);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_READ_CS_16, 0, 0, SDDF_PCIE_READ_CS_NUM_WORDS));

    sddf_pcie_status_t status = sddf_get_mr(0);
    if (status == SDDF_PCIE_STATUS_OK) {
        *value = sddf_get_mr(1);
    }
    return status;
}

static inline sddf_pcie_status_t sddf_pcie_read_config_space_32(unsigned int channel, sddf_pcie_handle_t handle,
                                                                uint16_t offset, uint32_t *value)
{
    sddf_set_mr(0, handle);
    sddf_set_mr(1, offset);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_READ_CS_32, 0, 0, SDDF_PCIE_READ_CS_NUM_WORDS));

    sddf_pcie_status_t status = sddf_get_mr(0);
    if (status == SDDF_PCIE_STATUS_OK) {
        *value = sddf_get_mr(1);
    }
    return status;
}

/**
 * Get the details of the device's `bar_index`th memory BAR.
 * A 64-bit BAR occupies two BAR slots and is referred to by the lower index.
 * @param channel ID of the PCIe driver.
 * @param handle handle of the claimed device.
 * @param bar_index index of the BAR, from 0 to 5.
 * @param bar_size on success, the size of the BAR in bytes.
 * @param is_64b on success, whether the BAR is 64-bit or not.
 * @param prefetchable on success, whether the BAR is prefetchable or not.
 * @return SDDF_PCIE_STATUS_OK on success,
 *         SDDF_PCIE_STATUS_INVALID_HANDLE if the handle is invalid,
 *         SDDF_PCIE_STATUS_NOT_FOUND if the device does not implement the BAR, or the high index of a 64-bit BAR was given,
 *         SDDF_PCIE_STATUS_INVALID_ARGUMENT if the bar index is out of bound.
 */
static inline sddf_pcie_status_t sddf_pcie_get_mem_bar(unsigned int channel, sddf_pcie_handle_t handle,
                                                       uint8_t bar_index, uint64_t *bar_size, bool *is_64b,
                                                       bool *prefetchable)
{
    sddf_set_mr(0, handle);
    sddf_set_mr(1, bar_index);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_GET_MEM_BAR, 0, 0, SDDF_PCIE_GET_MEM_BAR_NUM_WORDS));

    sddf_pcie_status_t status = sddf_get_mr(0);
    if (status == SDDF_PCIE_STATUS_OK) {
        *bar_size = sddf_get_mr(1);
        *is_64b = sddf_get_mr(2);
        *prefetchable = sddf_get_mr(3);
    }
    return status;
}

/**
 * Map the device's `bar_index`th memory BAR into the client's address space.
 * @param channel ID of the PCIe driver.
 * @param handle handle of the claimed device.
 * @param bar_index index of the BAR, from 0 to 5.
 * @param map_addr 4K page-aligned virtual address to map the BAR at.
 * @param attributes caching attributes of the mapping.
 * @param read_write true for a read-write mapping, false for read-only.
 * @return SDDF_PCIE_STATUS_OK on success,
 *         SDDF_PCIE_STATUS_INVALID_HANDLE if the handle is invalid,
 *         SDDF_PCIE_STATUS_NOT_FOUND if the device does not implement the BAR, or the BAR is not a memory BAR
 *         SDDF_PCIE_STATUS_FORBIDDEN if the BAR holds the MSI/MSI-X table,
 *         SDDF_PCIE_STATUS_MAPPING_FAILED if the address range is already in use.
 */
static inline sddf_pcie_status_t sddf_pcie_map_mem_bar(unsigned int channel, sddf_pcie_handle_t handle,
                                                       uint8_t bar_index, uint64_t map_addr,
                                                       sddf_pcie_mem_attr_t attributes, bool read_write)
{
    sddf_set_mr(0, handle);
    sddf_set_mr(1, bar_index);
    sddf_set_mr(2, map_addr);
    sddf_set_mr(3, attributes);
    sddf_set_mr(
        4,
        read_write); // @billn > 4 words = no fastpath, issue? can do bit packing? investigate later not a problem now
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_MAP_MEM_BAR, 0, 0, SDDF_PCIE_MAP_MEM_BAR_NUM_WORDS));

    sddf_pcie_status_t status = sddf_get_mr(0);
    return status;
}

/**
 * Route the device's legacy INTx interrupt to the client's channel `cid`.
 * INTx lines are shared between devices, so the interrupt goes to the PCIe driver first,
 * which then notifies the clients whose devices raised it. `ch_id` is therefore a normal
 * notification channel: do not call microkit_irq_ack() or sddf_irq_ack() on it,
 * call sddf_pcie_ack_intx() instead once the cause of the interrupt has been cleared in the device.
 * This is a lot of context switching and slow, so use MSI/MSI-X instead when the device supports it.
 * @param channel ID of the PCIe driver.
 * @param handle handle of the claimed device.
 * @param ch_id ID of the channel the client receives the interrupt on.
 * @return SDDF_PCIE_STATUS_OK on success,
 *         SDDF_PCIE_STATUS_INVALID_HANDLE if the handle is invalid,
 *         SDDF_PCIE_STATUS_NOT_FOUND if the device does not use INTx.
 */
static inline sddf_pcie_status_t sddf_pcie_map_intx(unsigned int channel, sddf_pcie_handle_t handle, uint64_t ch_id)
{
    sddf_set_mr(0, handle);
    sddf_set_mr(1, ch_id);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_MAP_INTX, 0, 0, SDDF_PCIE_MAP_INTX_NUM_WORDS));

    sddf_pcie_status_t status = sddf_get_mr(0);
    return status;
}

/**
 * Tell the PCIe driver that the device's INTx interrupt has been handled, so it can be
 * unmasked. Only call this after clearing the cause in the device, otherwise the interrupt
 * fires again immediately.
 * @param channel ID of the PCIe driver.
 * @param handle handle of the claimed device.
 * @return SDDF_PCIE_STATUS_OK on success.
 *         SDDF_PCIE_STATUS_INVALID_HANDLE if the handle is invalid.
 */
static inline sddf_pcie_status_t sddf_pcie_ack_intx(unsigned int channel, sddf_pcie_handle_t handle)
{
    sddf_set_mr(0, handle);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_ACK_INTX, 0, 0, SDDF_PCIE_ACK_INTX_NUM_WORDS));

    sddf_pcie_status_t status = sddf_get_mr(0);
    return status;
}

/* Map MSI, TODO, don't care for now */