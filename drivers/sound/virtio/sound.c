/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * This driver follows the non-legacy virtIO 1.2 specification for the sound device.
 * It assumes that the transport method is MMIO.
 * This driver is very minimal and was written for the goal of building systems that
 * use virtIO sound devices in a simulator like QEMU. It is *not* written with
 * performance in mind.
 *
 * It should also be noted that because this driver is intended to be used with a
 * simulator such as QEMU, things like memory fences when touching device registers
 * may be needed if instead this driver was to be used in a different environment.
 */

#include <os/sddf.h>
#include <sddf/util/ialloc.h>
#include <sddf/resources/device.h>
#include <sddf/virtio/transport/common.h>
#include <sddf/virtio/transport/pci.h>
#include <sddf/virtio/queue.h>
#include <sddf/virtio/feature.h>
#include "sound.h"

#define CTRL_QUEUE 0
#define EVENT_QUEUE 1
#define TX_QUEUE 2
#define RX_QUEUE 3

#define NUM_VIRTQ 4
#define VIRTQ_SIZE 128

virtio_device_handle_t dev;
static volatile struct virtq vqs[NUM_VIRTQ];
static struct virtio_snd_config *virtio_config;
static void *virtio_queues;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

static size_t virtq_alloc(struct virtq *virtq, uint32_t size, void *vaddr, size_t alloc_off)
{
    size_t desc_off = ALIGN(alloc_off, 16);
    size_t avail_off = ALIGN(desc_off + (16 * size), 2);
    size_t used_off = ALIGN(used_off + (6 + 2 * size), 4);

    virtq->num = size;
    virtq->desc = (struct virtq_desc *)(vaddr + desc_off);
    virtq->avail = (struct virtq_avail *)(vaddr + avail_off);
    virtq->used = (struct virtq_used *)(vaddr + used_off);

    assert((uintptr_t)virtq->desc % 16 == 0);
    assert((uintptr_t)virtq->avail % 2 == 0);
    assert((uintptr_t)virtq->used % 4 == 0);

    return used_off + (6 + 8 * size);
}

static void virtio_snd_init(void)
{
    assert(virtio_transport_probe(&device_resources, &dev, VIRTIO_DEVICE_ID_SOUND));
    // ialloc_init(&ialloc_desc, descriptors, QUEUE_SIZE);

    /* First reset the device */
    virtio_transport_set_status(&dev, 0);
    /* Set the ACKNOWLEDGE bit to say we have noticed the device */
    virtio_transport_set_status(&dev, VIRTIO_DEVICE_STATUS_ACKNOWLEDGE);
    /* Set the DRIVER bit to say we know how to drive the device */
    virtio_transport_set_status(&dev, VIRTIO_DEVICE_STATUS_DRIVER);

    virtio_config = (volatile struct virtio_snd_config *)virtio_transport_get_device_config(&dev);
#ifdef DEBUG_DRIVER
    virtio_snd_print_config(virtio_config);
#endif

    /* At the time of writing, there are no feature bits to negotiate specific to
     * the sound device. */
    virtio_transport_set_driver_features(&dev, 0, 0);
    virtio_transport_set_driver_features(&dev, 1, 0);
    virtio_transport_set_status(&dev, VIRTIO_DEVICE_STATUS_FEATURES_OK);
    if (!(virtio_transport_get_status(&dev) & VIRTIO_DEVICE_STATUS_FEATURES_OK)) {
        LOG_DRIVER_ERR("device status features is not OK!\n");
        return;
    }

    virtio_queues = device_resources.regions[1].region.vaddr;
    uint64_t virtio_queues_paddr = device_resources.regions[1].io_addr;
    size_t alloc_off = 0;
    for (int i = 0; i < NUM_VIRTQ; i++) {
        alloc_off = virtq_alloc(&vqs[i], VIRTQ_SIZE, virtio_queues, alloc_off);
        size_t desc_off = (void *)vqs[i].desc - virtio_queues;
        size_t avail_off = (void *)vqs[i].desc - virtio_queues;
        size_t used_off = (void *)vqs[i].desc - virtio_queues;
        virtio_transport_queue_setup(&dev, i, VIRTQ_SIZE, virtio_queues_paddr + desc_off, virtio_queues_paddr + avail_off,
                                 virtio_queues_paddr + used_off);
    }
    LOG_DRIVER("alloc_off: 0x%lx\n", alloc_off);
    assert(alloc_off <= device_resources.regions[1].region.size);


    /* Finish initialisation */
    virtio_transport_set_status(&dev, VIRTIO_DEVICE_STATUS_DRIVER_OK);
    virtio_transport_write_isr(&dev, VIRTIO_IRQ_VQUEUE);
}

void notified(sddf_channel ch)
{
}

void init(void)
{
    LOG_DRIVER("starting\n");

    // TODO: magic checks
    memcpy(device_resources.magic, DEVICE_MAGIC, DEVICE_MAGIC_LEN);
    device_resources.regions[0].region.vaddr = (void *)(0x20000000 + 0x3e00);
    device_resources.regions[0].region.size = 0x1000;
    device_resources.regions[1].region.vaddr = (void *)(0x30000000);
    device_resources.regions[1].region.size = 0x400000;
    device_resources.regions[1].io_addr = 0x50000000;

    virtio_snd_init();
}
