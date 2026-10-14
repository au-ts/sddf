/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

/* Maximum number of device specs per client. A client normally claims a single PCIe device,
 * and 8 specs covers every function of one multi-function device. Increase this if a driver
 * ever needs to claim several devices. */
#define SDDF_PCIE_MAX_DEVICE_SPECS_PER_CLIENT 8

#define SDDF_PCIE_MAX_CLIENTS 64

#define SDDF_PCIE_DEVICE_INSTANCE_ANY 0xFFFF
#define SDDF_PCIE_DEVICE_SPEC_VENDOR_ID_ANY 0xFFFF
#define SDDF_PCIE_DEVICE_SPEC_DEVICE_ID_ANY 0xFFFF
#define SDDF_PCIE_DEVICE_SPEC_FUNCTION_ID_ANY 0xFF
#define SDDF_PCIE_DEVICE_SPEC_CLASS_CODE_ANY 0xFFFFFFFF

typedef struct {
    uint16_t instance;       /* nth match in scan order, or SDDF_PCIE_DEVICE_INSTANCE_ANY */
    uint16_t vendor, device;
    uint8_t function;
    uint32_t class_code;     /* class:subclass:prog-if */
    uint8_t bus_master;      /* can DMA? If yes and x86 then the IOMMU needs to be set up,
                              * Microkit >= 2.3.0 turns on the Intel VT-d IOMMU by default. */
} pcie_device_spec_t;

typedef struct {
    uint8_t id;
    uint64_t vspace_slot;
    uint8_t vspace_is_x86_ept;
    uint64_t ntfn_slot;
    pcie_device_spec_t specs[SDDF_PCIE_MAX_DEVICE_SPECS_PER_CLIENT];
} pcie_connection_resource_t;

typedef struct {
    pcie_connection_resource_t clients[SDDF_PCIE_MAX_CLIENTS];
    uint64_t num_clients;
} pcie_driver_config_t;

// move below to protocol.h later
enum {
    SDDF_PCIE_CLAIM_DEVICE,
    SDDF_PCIE_READ_CS_8,
    SDDF_PCIE_READ_CS_16,
    SDDF_PCIE_READ_CS_32,
    SDDF_PCIE_GET_BAR,
    SDDF_PCIE_MAP_BAR,
    SDDF_PCIE_MAP_INTX,
    SDDF_PCIE_ACK_INTX,
};

// move below to client.h later

typedef enum {
    SDDF_PCIE_STATUS_OK = 0,
    SDDF_PCIE_STATUS_ALREADY_CLAIMED,
    SDDF_PCIE_STATUS_INVALID_HANDLE,
    SDDF_PCIE_STATUS_NOT_FOUND,
    SDDF_PCIE_STATUS_INVALID_ARGUMENT,
    SDDF_PCIE_STATUS_FORBIDDEN,
    SDDF_PCIE_STATUS_MAPPING_FAILED,
} sddf_pcie_status_t;

typedef int sddf_pcie_handle_t;

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
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_CLAIM_DEVICE, 0, 0, 1));

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
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_READ_CS_8, 0, 0, 2));

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
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_READ_CS_16, 0, 0, 2));

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
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_READ_CS_32, 0, 0, 2));

    sddf_pcie_status_t status = sddf_get_mr(0);
    if (status == SDDF_PCIE_STATUS_OK) {
        *value = sddf_get_mr(1);
    }
    return status;
}

/**
 * Get the details of the device's `bar_index`th BAR.
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
static inline sddf_pcie_status_t sddf_pcie_get_bar(unsigned int channel, sddf_pcie_handle_t handle, uint8_t bar_index,
                                                   uint64_t *bar_size, bool *is_64b, bool *prefetchable)
{
    sddf_set_mr(0, handle);
    sddf_set_mr(1, bar_index);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_GET_BAR, 0, 0, 2));

    sddf_pcie_status_t status = sddf_get_mr(0);
    if (status == SDDF_PCIE_STATUS_OK) {
        *bar_size = sddf_get_mr(1);
        *is_64b = sddf_get_mr(2);
        *prefetchable = sddf_get_mr(3);
    }
    return status;
}

typedef enum {
    SDDF_PCIE_MEM_CACHE_DISABLED = 0,
    SDDF_PCIE_MEM_CACHE_ENABLED = 1,
} sddf_pcie_mem_attr_t;

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
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_MAP_BAR, 0, 0, 5));

    sddf_pcie_status_t status = sddf_get_mr(0);
    return status;
}

/**
 * Route the device's legacy INTx interrupt to the client's channel `cid`.
 * INTx lines are shared between devices, so the interrupt goes to the PCIe driver first,
 * which then notifies the clients whose devices raised it. `cid` is therefore a normal
 * notification channel: do not call microkit_irq_ack() or sddf_irq_ack() on it,
 * call sddf_pcie_ack_intx() instead once the cause of the interrupt has been cleared in the device.
 * This is a lot of context switching and slow, so use MSI/MSI-X instead when the device supports it.
 * @param channel ID of the PCIe driver.
 * @param handle handle of the claimed device.
 * @param cid ID of the channel the client receives the interrupt on.
 * @return SDDF_PCIE_STATUS_OK on success,
 *         SDDF_PCIE_STATUS_INVALID_HANDLE if the handle is invalid,
 *         SDDF_PCIE_STATUS_NOT_FOUND if the device does not use INTx.
 */
static inline sddf_pcie_status_t sddf_pcie_map_intx(unsigned int channel, sddf_pcie_handle_t handle, uint64_t cid)
{
    sddf_set_mr(0, handle);
    sddf_set_mr(1, cid);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_MAP_INTX, 0, 0, 2));

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
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_PCIE_ACK_INTX, 0, 0, 1));

    sddf_pcie_status_t status = sddf_get_mr(0);
    return status;
}

/* Map MSI, TODO, don't care for now */