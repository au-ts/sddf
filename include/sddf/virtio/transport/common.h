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

typedef struct virtio_device_handle {
    device_resources_t *device_resources;
} virtio_device_handle_t;

bool virtio_transport_probe(device_resources_t *device_resources, virtio_device_handle_t *device_handle_ret);
void *virtio_transport_get_device_config(virtio_device_handle_t *device_handle);
void virtio_transport_set_status(virtio_device_handle_t *device_handle, uint8_t status);
uint8_t virtio_transport_get_status(virtio_device_handle_t *device_handle);
uint32_t virtio_transport_get_device_features(virtio_device_handle_t *device_handle, uint32_t select);
uint32_t virtio_transport_get_driver_features(virtio_device_handle_t *device_handle, uint32_t select);
void virtio_transport_set_driver_features(virtio_device_handle_t *device_handle, uint32_t select, uint32_t driver_features);
bool virtio_transport_queue_setup(virtio_device_handle_t *device_handle, uint32_t select, uint16_t size, uint64_t desc, uint64_t driver, uint64_t device);
void virtio_transport_queue_notify(virtio_device_handle_t *device_handle, uint32_t select);
uint32_t virtio_transport_read_isr(virtio_device_handle_t *device_handle);
void virtio_transport_write_isr(virtio_device_handle_t *device_handle, uint32_t isr);