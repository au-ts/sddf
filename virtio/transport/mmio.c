/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/virtio/transport/common.h>
#include <sddf/virtio/transport/mmio.h>
#include <sddf/resources/device.h>

static bool check_magic(virtio_mmio_regs_t *regs)
{
    return regs->MagicValue == 0x74726976;
}

static bool check_device_id(virtio_mmio_regs_t *regs, virtio_mmio_device_id_t id)
{
    return regs->DeviceID == id;
}

static uint32_t get_version(virtio_mmio_regs_t *regs)
{
    return regs->Version;
}

static volatile virtio_mmio_regs_t *get_regs(device_resources_t *device_resources)
{
    return (volatile virtio_mmio_regs_t *)device_resources->regions[0].region.vaddr;
}

bool virtio_transport_probe(device_resources_t *device_resources, virtio_device_handle_t *device_handle_ret)
{
    assert(device_resources_check_magic(device_resources));
    volatile virtio_mmio_regs_t *regs = get_regs(device_resources);

    // Do MMIO device init (section 4.2.3.1)
    if (!check_magic(regs)) {
        LOG_VIRTIO_TRANSPORT("invalid virtIO magic value!\n");
        return false;
    }

    if (get_version(regs) != VIRTIO_VERSION) {
        LOG_VIRTIO_TRANSPORT("not correct virtIO version!\n");
        return false;
    }

    // @billn double check
    // if (!virtio_mmio_check_device_id(regs, VIRTIO_DEVICE_ID_NET)) {
    //     LOG_VIRTIO_TRANSPORT("not a virtIO network device!\n");
    //     return false;
    // }

    device_handle_ret->device_resources = device_resources;
    return true;
}

void *virtio_transport_get_device_config(virtio_device_handle_t *device_handle)
{
    return (void *) (get_regs(device_handle->device_resources)->Config);
}

void virtio_transport_set_status(virtio_device_handle_t *device_handle, uint8_t status)
{
    volatile virtio_mmio_regs_t *regs = get_regs(device_handle->device_resources);
    regs->Status = (uint32_t) status;
}

uint8_t virtio_transport_get_status(virtio_device_handle_t *device_handle) {
    volatile virtio_mmio_regs_t *regs = get_regs(device_handle->device_resources);
    return (uint8_t) regs->Status;
}

uint32_t virtio_transport_get_device_features(virtio_device_handle_t *device_handle, uint32_t select)
{
    volatile virtio_mmio_regs_t *regs = get_regs(device_handle->device_resources);

    regs->DeviceFeaturesSel = select;
    return regs->DeviceFeatures;
}

uint32_t virtio_transport_get_driver_features(virtio_device_handle_t *device_handle, uint32_t select)
{
    volatile virtio_mmio_regs_t *regs = get_regs(device_handle->device_resources);

    regs->DriverFeaturesSel = select;
    return regs->DriverFeatures;
}

void virtio_transport_set_driver_features(virtio_device_handle_t *device_handle, uint32_t select, uint32_t driver_features)
{
    volatile virtio_mmio_regs_t *regs = get_regs(device_handle->device_resources);

    regs->DriverFeaturesSel = select;
    regs->DriverFeatures = driver_features;
}

bool virtio_transport_queue_setup(virtio_device_handle_t *device_handle, uint32_t select, uint16_t size, uint64_t desc, uint64_t driver, uint64_t device)
{
    volatile virtio_mmio_regs_t *regs = get_regs(device_handle->device_resources);

    regs->QueueSel = select;

    if (regs->QueueNumMax < size) {
        LOG_VIRTIO_TRANSPORT("virtio queue is smaller than virtqueue!\n");
        return false;
    }

    regs->QueueNum = (uint32_t) size;
    regs->QueueDescLow = desc & 0xffffffff;
    regs->QueueDescHigh = desc >> 32;
    regs->QueueDriverLow = driver & 0xffffffff;
    regs->QueueDriverHigh = driver >> 32;
    regs->QueueDeviceLow = device & 0xffffffff;
    regs->QueueDeviceHigh = device >> 32;
    regs->QueueReady = 1;

    return true;
}

void virtio_transport_queue_notify(virtio_device_handle_t *device_handle, uint32_t select)
{
    volatile virtio_mmio_regs_t *regs = get_regs(device_handle->device_resources);

    regs->QueueNotify = select;
}

uint32_t virtio_transport_read_isr(virtio_device_handle_t *device_handle)
{
    volatile virtio_mmio_regs_t *regs = get_regs(device_handle->device_resources);
    return regs->InterruptStatus;
}

void virtio_transport_write_isr(virtio_device_handle_t *device_handle, uint32_t isr)
{
    volatile virtio_mmio_regs_t *regs = get_regs(device_handle->device_resources);

    regs->InterruptACK = isr;
}