/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/resources/device.h>
#include <sddf/util/printf.h>

// #define DEBUG_VIRTIO_TRANSPORT

#ifdef DEBUG_VIRTIO_TRANSPORT
#define LOG_VIRTIO_TRANSPORT(...) do{ sddf_dprintf("VIRTIO TRANSPORT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_VIRTIO_TRANSPORT(...) do{}while(0)
#endif

#define LOG_VIRTIO_ERR(...) do{ sddf_dprintf("VIRTIO|ERR: "); sddf_dprintf(__VA_ARGS__); }while(0)

#define VIRTIO_VERSION (0x2)

#define VIRTIO_IRQ_VQUEUE  (1 << 0)
#define VIRTIO_IRQ_CONFIG  (1 << 1)

#define VIRTIO_DEVICE_STATUS_ACKNOWLEDGE (0x1)
#define VIRTIO_DEVICE_STATUS_DRIVER (0x2)
#define VIRTIO_DEVICE_STATUS_FAILED (0x80)
#define VIRTIO_DEVICE_STATUS_FEATURES_OK (0x8)
#define VIRTIO_DEVICE_STATUS_DRIVER_OK (0x4)
#define VIRTIO_DEVICE_STATUS_DRIVER_RESET (0x40)

typedef enum {
    VIRTIO_DEVICE_ID_NET = 0x1,
    VIRTIO_DEVICE_ID_BLK = 0x2,
    VIRTIO_DEVICE_ID_CONSOLE = 0x3,
    VIRTIO_DEVICE_ID_GPU = 0x10,
} virtio_device_id_t;

typedef struct virtio_device_handle {
    device_resources_t *device_resources;
    uint8_t pci_bus;
    uint8_t pci_dev;
    uint8_t pci_func;
    uint8_t pci_class_code;
    uint8_t pci_subclass;
    uint16_t pci_vendor_id;
    uint16_t pci_device_id;
} virtio_device_handle_t;

bool virtio_transport_probe(device_resources_t *device_resources, virtio_device_handle_t *device_handle_ret,
                            uint32_t device_id);
void *virtio_transport_get_device_config(virtio_device_handle_t *device_handle);
void virtio_transport_set_status(virtio_device_handle_t *device_handle, uint8_t status);
uint8_t virtio_transport_get_status(virtio_device_handle_t *device_handle);
uint32_t virtio_transport_get_device_features(virtio_device_handle_t *device_handle, uint32_t select);
uint32_t virtio_transport_get_driver_features(virtio_device_handle_t *device_handle, uint32_t select);
void virtio_transport_set_driver_features(virtio_device_handle_t *device_handle, uint32_t select,
                                          uint32_t driver_features);
bool virtio_transport_queue_setup(virtio_device_handle_t *device_handle, uint32_t select, uint16_t size, uint64_t desc,
                                  uint64_t driver, uint64_t device);
void virtio_transport_queue_notify(virtio_device_handle_t *device_handle, uint32_t select);
uint32_t virtio_transport_read_isr(virtio_device_handle_t *device_handle);
void virtio_transport_write_isr(virtio_device_handle_t *device_handle, uint32_t isr);
