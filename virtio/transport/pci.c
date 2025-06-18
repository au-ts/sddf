/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/virtio/common.h>
#include <sddf/virtio/transport/common.h>
#include <sddf/virtio/transport/pci.h>
#include <sddf/resources/device.h>

bool virtio_transport_probe(device_resources_t *device_resources, virtio_device_handle_t *device_handle_ret)
{
    assert(device_resources_check_magic(device_resources));
    // assert(device_resources->num_irqs == 1);
    // assert(device_resources->num_regions == 2);

    return false;
}

void *virtio_transport_get_device_config(virtio_device_handle_t *device_handle)
{
    return (void *) NULL;
}

void virtio_transport_set_status(virtio_device_handle_t *device_handle, uint8_t status)
{
    return;
}

uint8_t virtio_transport_get_status(virtio_device_handle_t *device_handle) {
    return 0;
}

uint32_t virtio_transport_get_device_features(virtio_device_handle_t *device_handle, uint32_t select)
{
    return 0;
}

uint32_t virtio_transport_get_driver_features(virtio_device_handle_t *device_handle, uint32_t select)
{
    return 0;
}

void virtio_transport_set_driver_features(virtio_device_handle_t *device_handle, uint32_t select, uint32_t driver_features)
{
    return;
}

bool virtio_transport_queue_setup(virtio_device_handle_t *device_handle, uint32_t select, uint16_t size, uint64_t desc, uint64_t driver, uint64_t device)
{
    return false;
}

void virtio_transport_queue_notify(virtio_device_handle_t *device_handle, uint32_t select)
{
    return;
}

uint32_t virtio_transport_read_isr(virtio_device_handle_t *device_handle)
{
    return 0;
}

void virtio_transport_write_isr(virtio_device_handle_t *device_handle, uint32_t isr)
{
    return;
}
