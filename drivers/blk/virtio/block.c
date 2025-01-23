/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * This driver follows the non-legacy virtIO 1.2 specification for the block device.
 * It assumes that the transport method is MMIO.
 * This driver is very minimal and was written for the goal of building systems that
 * use virtIO block devices in a simulator like QEMU. It is *not* written with
 * performance in mind.
 *
 * It should also be noted that because this driver is intended to be used with a
 * simulator such as QEMU, things like memory fences when touching device registers
 * may be needed if instead this driver was to be used in a different environment.
 */

#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/ialloc.h>
#include <sddf/virtio/virtio.h>
#include <sddf/virtio/virtio_queue.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/config.h>
#include <sddf/blk/storage_info.h>
#include <sddf/resources/device.h>
#include "block.h"

#define QUEUE_SIZE 1024
#define VIRTQ_NUM_REQUESTS QUEUE_SIZE

uintptr_t requests_paddr;
uintptr_t requests_vaddr;

static volatile virtio_mmio_regs_t *regs;

static volatile struct virtq virtq;
static blk_queue_handle_t blk_queue;

uintptr_t virtio_headers_paddr;
static struct virtio_blk_req *virtio_headers;

/*
 * A mapping from virtIO header index in the descriptor virtq ring, to the sDDF ID given
 * in the request. We need this mapping due to out of order operations.
 */
uint32_t virtio_header_to_id[QUEUE_SIZE];

/*
 * Due to the out-of-order nature of virtIO, we need a way of allocating indexes in a
 * non-linear way.
 */
ialloc_t ialloc_desc;
uint32_t descriptors[QUEUE_SIZE];

uint16_t last_seen_used = 0;

/* Block device configuration, populated during initiliastion. */
volatile struct virtio_blk_config *virtio_config;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".blk_driver_config"))) blk_driver_config_t config;

void handle_response(void)
{
    bool notify = false;

    uint16_t i = last_seen_used;
    uint16_t curr_idx = virtq.used->idx;
    while (i != curr_idx) {
        uint16_t virtq_idx = i % virtq.num;
        struct virtq_used_elem hdr_used = virtq.used->ring[virtq_idx];
        assert(virtq.desc[hdr_used.id].flags & VIRTQ_DESC_F_NEXT);

        struct virtq_desc hdr_desc = virtq.desc[hdr_used.id];
        LOG_DRIVER("response header addr: 0x%lx, len: %d\n", hdr_desc.addr, hdr_desc.len);

        assert(hdr_desc.len == VIRTIO_BLK_REQ_HDR_SIZE);
        struct virtio_blk_req *hdr = &virtio_headers[virtq_idx];
        virtio_blk_print_req(hdr);

        uint16_t data_desc_idx = virtq.desc[hdr_used.id].next;
        struct virtq_desc data_desc = virtq.desc[data_desc_idx % virtq.num];
        uint32_t data_len = data_desc.len;
#ifdef DEBUG_DRIVER
        uint64_t data_addr = data_desc.addr;
        LOG_DRIVER("response data addr: 0x%lx, data len: %d\n", data_addr, data_len);
#endif

        uint16_t footer_desc_idx = virtq.desc[data_desc_idx].next;

        blk_resp_status_t status;
        if (hdr->status == VIRTIO_BLK_S_OK) {
            status = BLK_RESP_OK;
        } else {
            status = BLK_RESP_ERR_UNSPEC;
        }
        int err = blk_enqueue_resp(&blk_queue, status, data_len / BLK_TRANSFER_SIZE, virtio_header_to_id[hdr_used.id]);
        assert(!err);

        /* Free up the descriptors we used */
        err = ialloc_free(&ialloc_desc, hdr_used.id);
        assert(!err);
        err = ialloc_free(&ialloc_desc, data_desc_idx);
        assert(!err);
        err = ialloc_free(&ialloc_desc, footer_desc_idx);
        assert(!err);

        i += 1;
        notify = true;
    }

    if (notify) {
        microkit_notify(config.virt.id);
    }

    last_seen_used = i;
}

void handle_request()
{
    /* Whether or not we notify the virtIO device to say something has changed
     * in the virtq. */
    bool virtio_queue_notify = false;

    /* Consume all requests and put them in the 'avail' ring of the virtq. We do not
     * dequeue unless we know we can put the request in the virtq. */
    while (!blk_queue_empty_req(&blk_queue) && ialloc_num_free(&ialloc_desc) >= 3) {
        blk_req_code_t req_code;
        uintptr_t phys_addr;
        uint64_t block_number;
        uint16_t count;
        uint32_t id;
        int err = blk_dequeue_req(&blk_queue, &req_code, &phys_addr, &block_number, &count, &id);
        assert(!err);

        /*
         * The block size sDDF expects is different to virtIO, so we must first convert the request
         * parameters to virtIO.
         */
        assert(BLK_TRANSFER_SIZE >= VIRTIO_BLK_SECTOR_SIZE);
        size_t virtio_block_number = block_number * (BLK_TRANSFER_SIZE / VIRTIO_BLK_SECTOR_SIZE);
        size_t virtio_count = count * (BLK_TRANSFER_SIZE / VIRTIO_BLK_SECTOR_SIZE);

        switch (req_code) {
        case BLK_REQ_READ:
        case BLK_REQ_WRITE: {
            /*
             * Read and write requests are almost identical with virtIO so we combine them
             * here to save a bit of code duplication.
             * Each sDDF read/write is split into three virtIO descriptors:
             *     * header
             *     * data
             *     * footer (status field of the header)
             *
             * This is a bit weird, but the reason it is done is so that we do not have to do
             * any copying to/from the sDDF data region. The 'data' is expected between some of
             * the fields in the header and so we have one descriptor for all the fields, then
             * a 'footer' descriptor with the single remaining field of the header
             * (the status field).
             *
             */

            /* It is the responsibility of the virtualiser to check that the request is valid,
             * so we just assert that the block number and count do not exceed the capacity. */
            assert(virtio_block_number + virtio_count <= virtio_config->capacity);

            if (req_code == BLK_REQ_READ) {
                LOG_DRIVER("handling read request with physical address 0x%lx, block_number: 0x%x, count: 0x%x, id: 0x%x\n",
                           phys_addr, block_number, count, id);
            } else {
                LOG_DRIVER("handling write request with physical address 0x%lx, block_number: 0x%x, count: 0x%x, id: 0x%x\n",
                           phys_addr, block_number, count, id);
            }

            uint32_t hdr_desc_idx = -1;
            uint32_t data_desc_idx = -1;
            uint32_t footer_desc_idx = -1;

            int err;
            err = ialloc_alloc(&ialloc_desc, &hdr_desc_idx);
            assert(!err && hdr_desc_idx != -1);
            err = ialloc_alloc(&ialloc_desc, &data_desc_idx);
            assert(!err && data_desc_idx != -1);
            err = ialloc_alloc(&ialloc_desc, &footer_desc_idx);
            assert(!err && footer_desc_idx != -1);

            uint16_t data_flags = VIRTQ_DESC_F_NEXT;
            uint16_t type;
            if (req_code == BLK_REQ_READ) {
                type = VIRTIO_BLK_T_IN;
                /* Doing a read request, so device needs to be able to write into the DMA region. */
                data_flags |= VIRTQ_DESC_F_WRITE;
            } else {
                type = VIRTIO_BLK_T_OUT;
            }

            struct virtio_blk_req *hdr = &virtio_headers[hdr_desc_idx];
            hdr->type = type;
            hdr->sector = virtio_block_number;

            virtq.desc[hdr_desc_idx] = (struct virtq_desc) {
                .addr = virtio_headers_paddr + (hdr_desc_idx * sizeof(struct virtio_blk_req)),
                .len = VIRTIO_BLK_REQ_HDR_SIZE,
                .flags = VIRTQ_DESC_F_NEXT,
                .next = data_desc_idx,
            };

            virtq.desc[data_desc_idx] = (struct virtq_desc) {
                .addr = phys_addr,
                .len = VIRTIO_BLK_SECTOR_SIZE * virtio_count,
                .flags = data_flags,
                .next = footer_desc_idx,
            };

            virtq.desc[footer_desc_idx] = (struct virtq_desc) {
                .addr = virtq.desc[hdr_desc_idx].addr + VIRTIO_BLK_REQ_HDR_SIZE,
                .len = 1,
                .flags = VIRTQ_DESC_F_WRITE,
            };

            virtq.avail->ring[virtq.avail->idx % virtq.num] = hdr_desc_idx;
            virtq.avail->idx++;
            virtio_queue_notify = true;

            virtio_header_to_id[hdr_desc_idx] = id;

            break;
        }
        case BLK_REQ_FLUSH: {
            int err = blk_enqueue_resp(&blk_queue, BLK_RESP_OK, 0, id);
            assert(!err);
            microkit_notify(config.virt.id);
            break;
        }
        case BLK_REQ_BARRIER: {
            int err = blk_enqueue_resp(&blk_queue, BLK_RESP_OK, 0, id);
            assert(!err);
            microkit_notify(config.virt.id);
            break;
        }
        default:
            /* The virtualiser should have sanitised the request code and so we should never get here. */
            LOG_DRIVER_ERR("unsupported request code: 0x%x\n", req_code);
            break;
        }
    }

    if (virtio_queue_notify) {
        regs->QueueNotify = 0;
    }
}

void handle_irq(void)
{
    uint32_t irq_status = regs->InterruptStatus;
    if (irq_status & VIRTIO_MMIO_IRQ_VQUEUE) {
        handle_response();
        regs->InterruptACK = VIRTIO_MMIO_IRQ_VQUEUE;
    }

    if (irq_status & VIRTIO_MMIO_IRQ_CONFIG) {
        LOG_DRIVER_ERR("unexpected change in configuration\n");
    }
}

void virtio_blk_init(void)
{
    // Do MMIO device init (section 4.2.3.1)
    if (!virtio_mmio_check_magic(regs)) {
        LOG_DRIVER_ERR("invalid virtIO magic value!\n");
        assert(false);
    }

    if (virtio_mmio_version(regs) != VIRTIO_VERSION) {
        LOG_DRIVER_ERR("not correct virtIO version!\n");
        assert(false);
    }

    if (!virtio_mmio_check_device_id(regs, VIRTIO_DEVICE_ID_BLK)) {
        LOG_DRIVER_ERR("not a virtIO block device!\n");
        assert(false);
    }

    if (virtio_mmio_version(regs) != VIRTIO_BLK_DRIVER_VERSION) {
        LOG_DRIVER_ERR("driver does not support given virtIO version: 0x%x\n", virtio_mmio_version(regs));
        assert(false);
    }

    ialloc_init(&ialloc_desc, descriptors, QUEUE_SIZE);

    /* First reset the device */
    regs->Status = 0;
    /* Set the ACKNOWLEDGE bit to say we have noticed the device */
    regs->Status = VIRTIO_DEVICE_STATUS_ACKNOWLEDGE;
    /* Set the DRIVER bit to say we know how to drive the device */
    regs->Status = VIRTIO_DEVICE_STATUS_DRIVER;

    virtio_config = (volatile struct virtio_blk_config *)regs->Config;
#ifdef DEBUG_DRIVER
    virtio_blk_print_config(virtio_config);
#endif

    if (virtio_config->capacity < BLK_TRANSFER_SIZE / VIRTIO_BLK_SECTOR_SIZE) {
        LOG_DRIVER_ERR("driver does not support device capacity smaller than 0x%x bytes"
                       " (device has capacity of 0x%lx bytes)\n",
                       BLK_TRANSFER_SIZE, virtio_config->capacity * VIRTIO_BLK_SECTOR_SIZE);
        assert(false);
    }

    /* This driver does not support Read-Only devices, so we always leave this as false */
    blk_storage_info_t *storage_info = config.virt.storage_info.vaddr;
    storage_info->read_only = false;
    storage_info->capacity = (virtio_config->capacity * VIRTIO_BLK_SECTOR_SIZE) / BLK_TRANSFER_SIZE;
    storage_info->cylinders = virtio_config->geometry.cylinders;
    storage_info->heads = virtio_config->geometry.heads;
    storage_info->blocks = virtio_config->geometry.sectors;
    storage_info->block_size = 1;
    storage_info->sector_size = VIRTIO_BLK_SECTOR_SIZE;

    /* Finished populating configuration */
    __atomic_store_n(&storage_info->ready, true, __ATOMIC_RELEASE);

#ifdef DEBUG_DRIVER
    uint32_t features_low = regs->DeviceFeatures;
    regs->DeviceFeaturesSel = 1;
    uint32_t features_high = regs->DeviceFeatures;
    uint64_t features = features_low | ((uint64_t)features_high << 32);
    virtio_blk_print_features(features);
#endif
    /* Select features we want from the device */
    regs->DriverFeatures = 0;
    regs->DriverFeaturesSel = 1;
    regs->DriverFeatures = 0;

    regs->Status |= VIRTIO_DEVICE_STATUS_FEATURES_OK;
    if (!(regs->Status & VIRTIO_DEVICE_STATUS_FEATURES_OK)) {
        LOG_DRIVER_ERR("device status features is not OK!\n");
        return;
    }

    /* Add virtqueues */
    size_t desc_off = 0;
    size_t avail_off = ALIGN(desc_off + (16 * VIRTQ_NUM_REQUESTS), 2);
    size_t used_off = ALIGN(avail_off + (6 + 2 * VIRTQ_NUM_REQUESTS), 4);
    size_t size = used_off + (6 + 8 * VIRTQ_NUM_REQUESTS);

    // Make sure that the metadata region is able to fit all the virtIO specific
    // extra data.
    assert(size <= device_resources.regions[2].region.size);

    virtq.num = VIRTQ_NUM_REQUESTS;
    virtq.desc = (struct virtq_desc *)(requests_vaddr + desc_off);
    virtq.avail = (struct virtq_avail *)(requests_vaddr + avail_off);
    virtq.used = (struct virtq_used *)(requests_vaddr + used_off);

    assert(regs->QueueNumMax >= VIRTQ_NUM_REQUESTS);
    regs->QueueSel = 0;
    regs->QueueNum = VIRTQ_NUM_REQUESTS;
    regs->QueueDescLow = (requests_paddr + desc_off) & 0xFFFFFFFF;
    regs->QueueDescHigh = (requests_paddr + desc_off) >> 32;
    regs->QueueDriverLow = (requests_paddr + avail_off) & 0xFFFFFFFF;
    regs->QueueDriverHigh = (requests_paddr + avail_off) >> 32;
    regs->QueueDeviceLow = (requests_paddr + used_off) & 0xFFFFFFFF;
    regs->QueueDeviceHigh = (requests_paddr + used_off) >> 32;
    regs->QueueReady = 1;

    /* Finish initialisation */
    regs->Status |= VIRTIO_DEVICE_STATUS_DRIVER_OK;
    regs->InterruptACK = VIRTIO_MMIO_IRQ_VQUEUE;
}

void init(void)
{
    assert(blk_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 3);

    regs = (volatile virtio_mmio_regs_t *)device_resources.regions[0].region.vaddr;
    requests_paddr = device_resources.regions[2].io_addr;
    requests_vaddr = (uintptr_t)device_resources.regions[2].region.vaddr;
    virtio_headers_paddr = (uintptr_t)device_resources.regions[1].io_addr;
    virtio_headers = (struct virtio_blk_req *)device_resources.regions[1].region.vaddr;

    assert(virtio_headers_paddr);
    assert(virtio_headers);
    assert(requests_paddr);
    assert(requests_vaddr);

    virtio_blk_init();

    blk_queue_init(&blk_queue, config.virt.req_queue.vaddr, config.virt.resp_queue.vaddr, config.virt.num_buffers);
}

void notified(microkit_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();
        microkit_deferred_irq_ack(ch);
        /*
         * It is possible that we could not enqueue all requests when being notified
         * by the virtualiser because we ran out of space, so we try again now that
         * we have received a response and have resources freed.
         */
        handle_request();
    } else if (ch == config.virt.id) {
        handle_request();
    } else {
        LOG_DRIVER_ERR("received notification from unknown channel: 0x%x\n", ch);
    }
}
