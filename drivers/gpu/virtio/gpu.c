/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * This driver follows the non-legacy virtIO 1.2 specification for the gpu device.
 * It assumes that the transport method is MMIO.
 * This driver implements unaccelerated 2D commands in the control queue.
 *
 * It should also be noted that because this driver is intended to be used with a
 * simulator such as QEMU, things like memory fences when touching device registers
 * may be needed if instead this driver was to be used in a different environment.
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>
#include <sddf/util/ialloc.h>
#include <sddf/virtio/virtio.h>
#include <sddf/virtio/virtio_queue.h>
#include <sddf/gpu/queue.h>
#include <sddf/gpu/events.h>
#include <gpu.h>
#include <gpu_config.h>

/* Uncomment this to enable debug logging */
#define DEBUG_GPU_VIRTIO_DRIVER

#if defined(DEBUG_GPU_VIRTIO_DRIVER)
#define LOG_GPU_VIRTIO_DRIVER(...) do{ sddf_dprintf("GPU_VIRTIO_DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_GPU_VIRTIO_DRIVER(...) do{}while(0)
#endif
#define LOG_GPU_VIRTIO_DRIVER_ERR(...) do{ sddf_dprintf("GPU_VIRTIO_DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

#define IRQ_CH 0
#define VIRT_CH 1

/*
 * This offset is the default for QEMU, but can change depending on
 * the configuration of QEMU and what other virtIO devices are being
 * used.
 */
#ifndef VIRTIO_MMIO_GPU_OFFSET
#define VIRTIO_MMIO_GPU_OFFSET (0xe00)
#endif

#define VIRTQ_QUEUE_SIZE GPU_QUEUE_CAPACITY_DRV

/* Size of data contained in a single descriptor */
#define VIRTIO_DATA_ENTRY_SIZE 2048
_Static_assert((uint64_t)VIRTIO_DATA_ENTRY_SIZE * (uint64_t)VIRTQ_QUEUE_SIZE <= GPU_VIRTIO_DATA_REGION_SIZE,
               "VIRTIO_DATA_ENTRY_SIZE * VIRTQ_QUEUE_SIZE must be less than or "
               "equal to GPU_VIRTIO_DATA_REGION_SIZE");

#define VIRTIO_DATA(idx) ((idx) * VIRTIO_DATA_ENTRY_SIZE + virtio_data)
#define VIRTIO_DATA_PADDR(idx) ((idx) * VIRTIO_DATA_ENTRY_SIZE + virtio_data_paddr)

#define VIRTIO_DATA_PADDR_TO_VADDR(paddr) ((uintptr_t)(paddr) + virtio_data - virtio_data_paddr)

#define VIRTIO_MAX_DESC_PER_REQ 3

#define BIT_LOW(n)  (1ul<<(n))
#define BIT_HIGH(n) (1ul<<(n - 32 ))

/* Microkit patched variables */
uintptr_t virtio_regs;
uintptr_t virtio_metadata;
uintptr_t virtio_metadata_paddr;
uintptr_t virtio_data;
uintptr_t virtio_data_paddr;
gpu_req_queue_t *gpu_req_queue;
gpu_resp_queue_t *gpu_resp_queue;
gpu_events_t *gpu_events;
uintptr_t gpu_driver_data;
uintptr_t gpu_client_data_paddr;

static volatile virtio_mmio_regs_t *regs;
static volatile struct virtio_gpu_config
    *virtio_config; /* gpu device configuration, populated by device during initialisation. */
static struct virtq virtq;
static gpu_queue_handle_t gpu_queue_h;

/* Store information between a request/response pair */
typedef struct reqbk {
    /* Store virtio request code so that when device responds, we can check whether
     * it has written into our virtIO header descriptor, which is marked as read-only.
     */
    enum virtio_gpu_ctrl_type virtio_code;
    /* Offset into sddf data memory region. Currently only DISPLAY_INFO requests
     * imply data written in the data region, which would need to be stored.
     */
    uint64_t mem_offset;
} reqbk_t;
static reqbk_t reqsbk[GPU_QUEUE_CAPACITY_DRV];

static ialloc_t ialloc_desc;
static uint32_t ialloc_desc_idxlist[VIRTQ_QUEUE_SIZE];
/* Mapping from virtIO descriptor idx to sDDF id */
static uint32_t virtio_desc_to_id[VIRTQ_QUEUE_SIZE];

static uint16_t last_handled_used_idx = 0;

static void virtio_gpu_init();
static void handle_request();
static void handle_irq();

void init(void)
{
    LOG_GPU_VIRTIO_DRIVER("Initialising GPU virtio driver!\n");
    ialloc_init(&ialloc_desc, ialloc_desc_idxlist, VIRTQ_QUEUE_SIZE);

    gpu_queue_init(&gpu_queue_h, gpu_req_queue, gpu_resp_queue, GPU_QUEUE_CAPACITY_DRV);

    regs = (volatile virtio_mmio_regs_t *)(virtio_regs + VIRTIO_MMIO_GPU_OFFSET);
    virtio_config = (volatile struct virtio_gpu_config *)regs->Config;
    virtio_gpu_init();
}

void notified(microkit_channel ch)
{
#ifdef DEBUG_GPU_VIRTIO_DRIVER
    if (ch == IRQ_CH) {
        LOG_GPU_VIRTIO_DRIVER("Received interrupt from device\n");
    } else {
        LOG_GPU_VIRTIO_DRIVER("Received notification from virtualiser\n");
    }
#endif
    switch (ch) {
    case IRQ_CH:
        handle_irq();
        microkit_deferred_irq_ack(ch);
        break;
    case VIRT_CH:
        handle_request();
        break;
    default:
        LOG_GPU_VIRTIO_DRIVER_ERR("Received notification from unknown channel: 0x%x\n", ch);
    }
}

static void virtio_gpu_init(void)
{
    /* Do MMIO device init (section 4.2.3.1) */
    if (!virtio_mmio_check_magic(regs)) {
        LOG_GPU_VIRTIO_DRIVER_ERR("Invalid virtIO magic value!\n");
        assert(false);
    }

    if (virtio_mmio_version(regs) != VIRTIO_VERSION) {
        LOG_GPU_VIRTIO_DRIVER_ERR("Incorrect virtIO version!\n");
        assert(false);
    }

    if (!virtio_mmio_check_device_id(regs, VIRTIO_DEVICE_ID_GPU)) {
        LOG_GPU_VIRTIO_DRIVER_ERR("Not a virtIO gpu device!\n");
        assert(false);
    }

    if (virtio_mmio_version(regs) != VIRTIO_GPU_DRIVER_VERSION) {
        LOG_GPU_VIRTIO_DRIVER_ERR("Driver does not support given virtIO version: 0x%x\n", virtio_mmio_version(regs));
        LOG_GPU_VIRTIO_DRIVER_ERR("Driver supports virtIO version: 0x%x\n", VIRTIO_GPU_DRIVER_VERSION);
        assert(false);
    }

    /* First reset the device */
    regs->Status = 0;
    /* Set the ACKNOWLEDGE bit to say we have noticed the device */
    regs->Status = VIRTIO_DEVICE_STATUS_ACKNOWLEDGE;
    /* Set the DRIVER bit to say we know how to drive the device */
    regs->Status = VIRTIO_DEVICE_STATUS_DRIVER;

    /* Now we can read configuration space to validate its fields */
    if (virtio_config->num_scanouts == 0) {
        LOG_GPU_VIRTIO_DRIVER_ERR("No scanouts available!\n");
        assert(false);
    }

    uint32_t dev_features_low = regs->DeviceFeatures;
    regs->DeviceFeaturesSel = 1;
    uint32_t dev_features_high = regs->DeviceFeatures;

#ifdef DEBUG_GPU_VIRTIO_DRIVER
    LOG_GPU_VIRTIO_DRIVER("Device is offering the following features:\n");
    uint64_t dev_features = dev_features_low | ((uint64_t)dev_features_high << 32);
    virtio_print_reserved_feature_bits(dev_features);
    virtio_gpu_print_features(dev_features);
#endif

    /* Select features we want from the device.
     * We require blob resources for zero copy if enabled, and virtIO version 1
     * as we are following the non-legacy virtIO 1.2 specification.
     */
#ifdef GPU_BLOB_SUPPORT
    if (!(dev_features_low & BIT_LOW(VIRTIO_GPU_F_RESOURCE_BLOB))) {
        LOG_GPU_VIRTIO_DRIVER_ERR("Device does not support blob resources!\n");
        assert(false);
    }
#endif
    if (!(dev_features_high & BIT_HIGH(VIRTIO_F_VERSION_1))) {
        LOG_GPU_VIRTIO_DRIVER_ERR("Device does not support virtIO version 1!\n");
        assert(false);
    }
#ifdef GPU_BLOB_SUPPORT
    uint32_t drv_features_low = BIT_LOW(VIRTIO_GPU_F_RESOURCE_BLOB);
#else
    uint32_t drv_features_low = 0;
#endif
    uint32_t drv_features_high = BIT_HIGH(VIRTIO_F_VERSION_1);
    regs->DriverFeatures = drv_features_low;
    regs->DriverFeaturesSel = 1;
    regs->DriverFeatures = drv_features_high;

#ifdef DEBUG_GPU_VIRTIO_DRIVER
    uint64_t drv_features = drv_features_low | ((uint64_t)drv_features_high << 32);
    LOG_GPU_VIRTIO_DRIVER("Driver is selecting the following features:\n");
    virtio_print_reserved_feature_bits(drv_features);
    virtio_gpu_print_features(drv_features);
#endif

    regs->Status |= VIRTIO_DEVICE_STATUS_FEATURES_OK;
    if (!(regs->Status & VIRTIO_DEVICE_STATUS_FEATURES_OK)) {
        LOG_GPU_VIRTIO_DRIVER_ERR("Device status features is not OK!\n");
        assert(false);
    }

    /* Add virtqueues */
    size_t desc_off = 0;
    size_t avail_off = ALIGN(desc_off + (16 * VIRTQ_QUEUE_SIZE), 2);
    size_t used_off = ALIGN(avail_off + (6 + 2 * VIRTQ_QUEUE_SIZE), 4);
    size_t size = used_off + (6 + 8 * VIRTQ_QUEUE_SIZE);
    assert(size <= GPU_VIRTIO_METADATA_REGION_SIZE);

    virtq.num = VIRTQ_QUEUE_SIZE;
    virtq.desc = (struct virtq_desc *)(virtio_metadata + desc_off);
    virtq.avail = (struct virtq_avail *)(virtio_metadata + avail_off);
    virtq.used = (struct virtq_used *)(virtio_metadata + used_off);

    assert(regs->QueueNumMax >= VIRTQ_QUEUE_SIZE);
    regs->QueueSel = VIRTIO_GPU_CONTROL_QUEUE;
    regs->QueueNum = VIRTQ_QUEUE_SIZE;
    regs->QueueDescLow = (virtio_metadata_paddr + desc_off) & 0xFFFFFFFFUL;
    regs->QueueDescHigh = (virtio_metadata_paddr + desc_off) >> 32;
    regs->QueueDriverLow = (virtio_metadata_paddr + avail_off) & 0xFFFFFFFFUL;
    regs->QueueDriverHigh = (virtio_metadata_paddr + avail_off) >> 32;
    regs->QueueDeviceLow = (virtio_metadata_paddr + used_off) & 0xFFFFFFFFUL;
    regs->QueueDeviceHigh = (virtio_metadata_paddr + used_off) >> 32;
    regs->QueueReady = 1;

    /* Finish initialisation */
    regs->Status |= VIRTIO_DEVICE_STATUS_DRIVER_OK;
}

static gpu_resp_status_t virtio_gpu_to_sddf_resp_status(enum virtio_gpu_ctrl_type type)
{
    switch (type) {
    case VIRTIO_GPU_RESP_OK_DISPLAY_INFO:
    /* FALLTHROUGH */
    case VIRTIO_GPU_RESP_OK_NODATA:
        return GPU_RESP_OK;
    case VIRTIO_GPU_RESP_ERR_INVALID_RESOURCE_ID:
        return GPU_RESP_ERR_INVALID_RESOURCE_ID;
    case VIRTIO_GPU_RESP_ERR_INVALID_SCANOUT_ID:
        return GPU_RESP_ERR_INVALID_SCANOUT_ID;
    case VIRTIO_GPU_RESP_ERR_INVALID_PARAMETER:
        return GPU_RESP_ERR_INVALID_PARAMETER;
    case VIRTIO_GPU_RESP_ERR_OUT_OF_MEMORY:
    /* FALLTHROUGH */
    case VIRTIO_GPU_RESP_ERR_INVALID_CONTEXT_ID:
    /* FALLTHROUGH */
    case VIRTIO_GPU_RESP_ERR_UNSPEC:
        return GPU_RESP_ERR_UNSPEC;
    default:
        LOG_GPU_VIRTIO_DRIVER_ERR("Unexpected virtIO response type received from device: 0x%x\n", type);
        assert(false);
        return GPU_RESP_ERR_UNSPEC;
    }
}

static enum virtio_gpu_formats sddf_to_virtio_gpu_resource_format(gpu_formats_t format)
{
    switch (format) {
    case GPU_FORMAT_B8G8R8A8_UNORM:
                return VIRTIO_GPU_FORMAT_B8G8R8A8_UNORM;
    case GPU_FORMAT_B8G8R8X8_UNORM:
        return VIRTIO_GPU_FORMAT_B8G8R8X8_UNORM;
    case GPU_FORMAT_A8R8G8B8_UNORM:
        return VIRTIO_GPU_FORMAT_A8R8G8B8_UNORM;
    case GPU_FORMAT_X8R8G8B8_UNORM:
        return VIRTIO_GPU_FORMAT_X8R8G8B8_UNORM;
    case GPU_FORMAT_R8G8B8A8_UNORM:
        return VIRTIO_GPU_FORMAT_R8G8B8A8_UNORM;
    case GPU_FORMAT_R8G8B8X8_UNORM:
        return VIRTIO_GPU_FORMAT_R8G8B8X8_UNORM;
    case GPU_FORMAT_A8B8G8R8_UNORM:
        return VIRTIO_GPU_FORMAT_A8B8G8R8_UNORM;
    case GPU_FORMAT_X8B8G8R8_UNORM:
        return VIRTIO_GPU_FORMAT_X8B8G8R8_UNORM;
    default:
        LOG_GPU_VIRTIO_DRIVER_ERR("Unexpected sDDF resource format: 0x%x\n", format);
        assert(false);
        return VIRTIO_GPU_FORMAT_B8G8R8A8_UNORM;
    }
}

static bool handle_response()
{
    int err = 0;
    bool sddf_notify = false;
    uint16_t i = last_handled_used_idx;
    uint16_t curr_idx = virtq.used->idx;
    while (i != curr_idx) {
        struct virtq_used_elem used = virtq.used->ring[i % virtq.num];
        assert(used.id < VIRTQ_QUEUE_SIZE);

        LOG_GPU_VIRTIO_DRIVER("Handling response %d\n", virtio_desc_to_id[used.id]);

        struct virtq_desc desc_head = virtq.desc[used.id];
        assert(desc_head.len >= sizeof(struct virtio_gpu_ctrl_hdr));
        assert(desc_head.flags & VIRTQ_DESC_F_NEXT);
        assert(desc_head.next < VIRTQ_QUEUE_SIZE);

        gpu_resp_t resp = { 0 };
        resp.id = virtio_desc_to_id[used.id];
        resp.status = GPU_RESP_ERR_UNSPEC;

        struct virtio_gpu_ctrl_hdr *req_hdr = (struct virtio_gpu_ctrl_hdr *)VIRTIO_DATA_PADDR_TO_VADDR(desc_head.addr);
        assert(req_hdr->type == reqsbk[resp.id].virtio_code);
        switch (req_hdr->type) {
        case VIRTIO_GPU_CMD_GET_DISPLAY_INFO: {
            struct virtq_desc desc_footer = virtq.desc[desc_head.next];
            assert(desc_footer.len >= sizeof(struct virtio_gpu_resp_display_info));
            assert(desc_footer.flags & VIRTQ_DESC_F_WRITE);
            struct virtio_gpu_resp_display_info *resp_display_info =
                (struct virtio_gpu_resp_display_info *)VIRTIO_DATA_PADDR_TO_VADDR(desc_footer.addr);
            assert(resp_display_info->hdr.fence_id == req_hdr->fence_id);
            resp.status = virtio_gpu_to_sddf_resp_status(resp_display_info->hdr.type);

            struct gpu_resp_get_display_info *resp_display_info_sddf =
                (struct gpu_resp_get_display_info *)(reqsbk[resp.id].mem_offset + gpu_driver_data);
            int num_scanouts = (virtio_config->num_scanouts < GPU_MAX_SCANOUTS) ? virtio_config->num_scanouts
                               : GPU_MAX_SCANOUTS;
            for (int i = 0; i < num_scanouts; i++) {
                resp_display_info_sddf->scanouts[i].rect.x = resp_display_info->pmodes[i].r.x;
                resp_display_info_sddf->scanouts[i].rect.y = resp_display_info->pmodes[i].r.y;
                resp_display_info_sddf->scanouts[i].rect.width = resp_display_info->pmodes[i].r.width;
                resp_display_info_sddf->scanouts[i].rect.height = resp_display_info->pmodes[i].r.height;
                resp_display_info_sddf->scanouts[i].enabled = resp_display_info->pmodes[i].enabled;
            }
            resp_display_info_sddf->num_scanouts = num_scanouts;
            break;
        }
#ifdef GPU_BLOB_SUPPORT
        case VIRTIO_GPU_CMD_RESOURCE_CREATE_BLOB: {
            struct virtq_desc desc_body = virtq.desc[desc_head.next];
            assert(desc_body.flags & VIRTQ_DESC_F_NEXT);
            assert(desc_body.len >= sizeof(struct virtio_gpu_mem_entry));

            struct virtq_desc desc_footer = virtq.desc[desc_body.next];
            assert(desc_footer.len >= sizeof(struct virtio_gpu_ctrl_hdr));
            assert(desc_footer.flags & VIRTQ_DESC_F_WRITE);

            struct virtio_gpu_ctrl_hdr *resp_hdr = (struct virtio_gpu_ctrl_hdr *)VIRTIO_DATA_PADDR_TO_VADDR(
                                                       desc_footer.addr);
            assert(resp_hdr->fence_id == req_hdr->fence_id);
            resp.status = virtio_gpu_to_sddf_resp_status(resp_hdr->type);
            assert(desc_body.flags & VIRTQ_DESC_F_NEXT);
            assert(desc_body.len >= sizeof(struct virtio_gpu_mem_entry));

            err = ialloc_free(&ialloc_desc, desc_body.next);
            assert(!err);
            break;
        }
#endif
        case VIRTIO_GPU_CMD_RESOURCE_ATTACH_BACKING: {
            struct virtq_desc desc_body = virtq.desc[desc_head.next];
            assert(desc_body.flags & VIRTQ_DESC_F_NEXT);
            assert(desc_body.len >= sizeof(struct virtio_gpu_mem_entry));

            struct virtq_desc desc_footer = virtq.desc[desc_body.next];
            assert(desc_footer.len >= sizeof(struct virtio_gpu_ctrl_hdr));
            assert(desc_footer.flags & VIRTQ_DESC_F_WRITE);

            struct virtio_gpu_ctrl_hdr *resp_hdr = (struct virtio_gpu_ctrl_hdr *)VIRTIO_DATA_PADDR_TO_VADDR(
                                                       desc_footer.addr);
            assert(resp_hdr->fence_id == req_hdr->fence_id);
            resp.status = virtio_gpu_to_sddf_resp_status(resp_hdr->type);
            assert(desc_body.flags & VIRTQ_DESC_F_NEXT);
            assert(desc_body.len >= sizeof(struct virtio_gpu_mem_entry));

            err = ialloc_free(&ialloc_desc, desc_body.next);
            assert(!err);
            break;
        }
        case VIRTIO_GPU_CMD_RESOURCE_CREATE_2D:
        /* FALLTHROUGH */
#ifdef GPU_BLOB_SUPPORT
        case VIRTIO_GPU_CMD_SET_SCANOUT_BLOB:
        /* FALLTHROUGH */
#endif
        case VIRTIO_GPU_CMD_RESOURCE_UNREF:
        /* FALLTHROUGH */
        case VIRTIO_GPU_CMD_RESOURCE_DETACH_BACKING:
        /* FALLTHROUGH */
        case VIRTIO_GPU_CMD_SET_SCANOUT:
        /* FALLTHROUGH */
        case VIRTIO_GPU_CMD_TRANSFER_TO_HOST_2D:
        /* FALLTHROUGH */
        case VIRTIO_GPU_CMD_RESOURCE_FLUSH: {
            struct virtq_desc desc_footer = virtq.desc[desc_head.next];
            assert(desc_footer.len >= sizeof(struct virtio_gpu_ctrl_hdr));
            assert(desc_footer.flags & VIRTQ_DESC_F_WRITE);
            struct virtio_gpu_ctrl_hdr *resp_hdr = (struct virtio_gpu_ctrl_hdr *)VIRTIO_DATA_PADDR_TO_VADDR(
                                                       desc_footer.addr);
            assert(resp_hdr->fence_id == req_hdr->fence_id);
            resp.status = virtio_gpu_to_sddf_resp_status(resp_hdr->type);
            break;
        }
        default:
            /* This should never happen as we have already checked for a valid request
             * code when the request was made, and also whether the device has tampered with it.
             */
            LOG_GPU_VIRTIO_DRIVER_ERR("Unrecognised (but already sanitised) bookkept request code "
                                      "when processing response\n");
            assert(false);
            break;
        }

        err = ialloc_free(&ialloc_desc, used.id);
        assert(!err);
        err = ialloc_free(&ialloc_desc, desc_head.next);
        assert(!err);

        if (gpu_queue_full_resp(&gpu_queue_h)) {
            LOG_GPU_VIRTIO_DRIVER_ERR("Response queue is full, dropping response\n");
            continue;
        }

        err = gpu_enqueue_resp(&gpu_queue_h, resp);
        assert(!err);
        sddf_notify = true;

        i++;
    }

    last_handled_used_idx = i;

    return sddf_notify;
}

static void handle_request()
{
    int err = 0;
    bool virtio_queue_notify = false;
    bool sddf_notify = false;
    gpu_req_t req = { 0 };
    while (!gpu_queue_empty_req(&gpu_queue_h)) {
        if (ialloc_num_free(&ialloc_desc) < VIRTIO_MAX_DESC_PER_REQ) {
            LOG_GPU_VIRTIO_DRIVER("Not enough free descriptors\n");
            break;
        }

        err = gpu_dequeue_req(&gpu_queue_h, &req);
        assert(!err);

        LOG_GPU_VIRTIO_DRIVER("Handling request %d\n", req.id);

        /* VirtIO gpu requests contain a header for request metadata, and a footer for the response.
         * We allocate one descriptor for each. Some requests may require additional descriptors for
         * data. Here we allocate the necessary descriptors and convert the sDDF request into a virtIO
         * request.
         */

        uint32_t desc_head_idx = 0;
        err = ialloc_alloc(&ialloc_desc, &desc_head_idx);
        assert(!err);
        assert(desc_head_idx < VIRTQ_QUEUE_SIZE);

        virtio_desc_to_id[desc_head_idx] = req.id;

        virtq.desc[desc_head_idx].addr = (uint64_t)VIRTIO_DATA_PADDR(desc_head_idx);
        virtq.desc[desc_head_idx].len = 0;
        virtq.desc[desc_head_idx].flags = 0;

        virtq.avail->ring[virtq.avail->idx % virtq.num] = desc_head_idx;
        virtq.avail->idx++;

        uint32_t desc_footer_idx = 0;
        err = ialloc_alloc(&ialloc_desc, &desc_footer_idx);
        assert(!err);
        assert(desc_footer_idx < VIRTQ_QUEUE_SIZE);

        virtq.desc[desc_footer_idx].addr = (uint64_t)VIRTIO_DATA_PADDR(desc_footer_idx);
        virtq.desc[desc_footer_idx].len = 0;
        virtq.desc[desc_footer_idx].flags = VIRTQ_DESC_F_WRITE;

        switch (req.code) {
        case GPU_REQ_GET_DISPLAY_INFO: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_GET_DISPLAY_INFO;
            struct virtio_gpu_ctrl_hdr *hdr = (struct virtio_gpu_ctrl_hdr *)VIRTIO_DATA(desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            hdr->type = VIRTIO_GPU_CMD_GET_DISPLAY_INFO;
            hdr->flags = VIRTIO_GPU_FLAG_FENCE;
            hdr->fence_id = 0;

            virtq.desc[desc_head_idx].next = desc_footer_idx;
            virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_resp_display_info);

            reqsbk[req.id].mem_offset = req.get_display_info.mem_offset;
            break;
        }
#ifdef GPU_BLOB_SUPPORT
        case GPU_REQ_RESOURCE_CREATE_BLOB: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_RESOURCE_CREATE_BLOB;
            struct virtio_gpu_resource_create_blob *resource_create_blob =
                (struct virtio_gpu_resource_create_blob *)VIRTIO_DATA(desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_resource_create_blob);
            resource_create_blob->hdr.type = VIRTIO_GPU_CMD_RESOURCE_CREATE_BLOB;
            resource_create_blob->hdr.flags = VIRTIO_GPU_FLAG_FENCE;
            resource_create_blob->hdr.fence_id = 0;
            resource_create_blob->resource_id = req.resource_create_blob.resource_id;
            /* Type of blob resource memory: Guest only, Guest + Host, Host only. We use guest only */
            resource_create_blob->blob_mem = VIRTIO_GPU_BLOB_MEM_GUEST;
            /* Resource use purpose: memory access, sharing with driver instances, or sharing with other devices.
             * We use it for memory access purposes.
             */
            resource_create_blob->blob_flags = VIRTIO_GPU_BLOB_FLAG_USE_MAPPABLE;
            /* Rendering context id, unused in 2d */
            resource_create_blob->blob_id = 0;
            if (req.resource_create_blob.mem_size > 0) {
                resource_create_blob->nr_entries = 1;
                /* Page alignment needed by qemu blob udmabuf, it will let the request succeed and leave only a warning (???) */
                uint32_t memsize = ALIGN(req.resource_create_blob.mem_size, 4096);
                resource_create_blob->size = memsize;

                uint32_t desc_body_idx = 0;
                err = ialloc_alloc(&ialloc_desc, &desc_body_idx);
                assert(!err);
                assert(desc_body_idx < VIRTQ_QUEUE_SIZE);

                virtq.desc[desc_head_idx].next = desc_body_idx;
                virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

                virtq.desc[desc_body_idx].addr = (uint64_t)VIRTIO_DATA_PADDR(desc_body_idx);
                virtq.desc[desc_body_idx].len = sizeof(struct virtio_gpu_mem_entry);

                struct virtio_gpu_mem_entry *mem_entry = (struct virtio_gpu_mem_entry *)VIRTIO_DATA(desc_body_idx);
                mem_entry->addr = req.resource_create_blob.mem_offset + gpu_client_data_paddr;
                mem_entry->length = memsize;

                virtq.desc[desc_body_idx].next = desc_footer_idx;
                virtq.desc[desc_body_idx].flags = VIRTQ_DESC_F_NEXT;
            } else {
                resource_create_blob->nr_entries = 0;
                resource_create_blob->size = 0;
                virtq.desc[desc_head_idx].next = desc_footer_idx;
                virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;   
            }
            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            break;
        }
        case GPU_REQ_SET_SCANOUT_BLOB: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_SET_SCANOUT_BLOB;
            struct virtio_gpu_set_scanout_blob *set_scanout_blob = (struct virtio_gpu_set_scanout_blob *)VIRTIO_DATA(
                                                                       desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_set_scanout_blob);
            set_scanout_blob->hdr.type = VIRTIO_GPU_CMD_SET_SCANOUT_BLOB;
            set_scanout_blob->hdr.flags = VIRTIO_GPU_FLAG_FENCE;
            set_scanout_blob->hdr.fence_id = 0;
            set_scanout_blob->r.x = req.set_scanout_blob.rect.x;
            set_scanout_blob->r.y = req.set_scanout_blob.rect.y;
            set_scanout_blob->r.width = req.set_scanout_blob.rect.width;
            set_scanout_blob->r.height = req.set_scanout_blob.rect.height;
            set_scanout_blob->resource_id = req.set_scanout_blob.resource_id;
            set_scanout_blob->scanout_id = req.set_scanout_blob.scanout_id;
            set_scanout_blob->width = req.set_scanout_blob.width;
            set_scanout_blob->height = req.set_scanout_blob.height;
            set_scanout_blob->format = sddf_to_virtio_gpu_resource_format(req.set_scanout_blob.format);
            for (int i = 0; i < 4; i++) {
                set_scanout_blob->strides[i] = 0;
                set_scanout_blob->offsets[i] = 0;
            }
            set_scanout_blob->strides[0] = req.set_scanout_blob.stride;
            set_scanout_blob->offsets[0] = req.set_scanout_blob.offset;

            virtq.desc[desc_head_idx].next = desc_footer_idx;
            virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            break;
        }
#endif
        case GPU_REQ_RESOURCE_CREATE_2D: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_RESOURCE_CREATE_2D;
            struct virtio_gpu_resource_create_2d *resource_create_2d =
                (struct virtio_gpu_resource_create_2d *)VIRTIO_DATA(desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_resource_create_2d);
            resource_create_2d->hdr.type = VIRTIO_GPU_CMD_RESOURCE_CREATE_2D;
            resource_create_2d->hdr.flags = VIRTIO_GPU_FLAG_FENCE;
            resource_create_2d->hdr.fence_id = 0;
            resource_create_2d->width = req.resource_create_2d.width;
            resource_create_2d->height = req.resource_create_2d.height;
            resource_create_2d->format = sddf_to_virtio_gpu_resource_format(req.resource_create_2d.format);

            assert(req.resource_create_2d.resource_id != GPU_DISABLE_SCANOUT_RESOURCE_ID);
            resource_create_2d->resource_id = req.resource_create_2d.resource_id;

            virtq.desc[desc_head_idx].next = desc_footer_idx;
            virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            break;
        }
        case GPU_REQ_RESOURCE_UNREF: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_RESOURCE_UNREF;
            struct virtio_gpu_resource_unref *resource_unref = (struct virtio_gpu_resource_unref *)VIRTIO_DATA(
                                                                   desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_resource_unref);
            resource_unref->hdr.type = VIRTIO_GPU_CMD_RESOURCE_UNREF;
            resource_unref->hdr.flags = VIRTIO_GPU_FLAG_FENCE;
            resource_unref->hdr.fence_id = 0;
            resource_unref->resource_id = req.resource_unref.resource_id;

            virtq.desc[desc_head_idx].next = desc_footer_idx;
            virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            break;
        }
        case GPU_REQ_RESOURCE_ATTACH_BACKING: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_RESOURCE_ATTACH_BACKING;
            struct virtio_gpu_resource_attach_backing *resource_attach_backing =
                (struct virtio_gpu_resource_attach_backing *)VIRTIO_DATA(desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_resource_attach_backing);
            resource_attach_backing->hdr.type = VIRTIO_GPU_CMD_RESOURCE_ATTACH_BACKING;
            resource_attach_backing->hdr.flags = VIRTIO_GPU_FLAG_FENCE;
            resource_attach_backing->hdr.fence_id = 0;
            resource_attach_backing->resource_id = req.resource_attach_backing.resource_id;
            resource_attach_backing->nr_entries = 1;

            uint32_t desc_body_idx = 0;
            err = ialloc_alloc(&ialloc_desc, &desc_body_idx);
            assert(!err);
            assert(desc_body_idx < VIRTQ_QUEUE_SIZE);

            virtq.desc[desc_head_idx].next = desc_body_idx;
            virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_body_idx].addr = (uint64_t)VIRTIO_DATA_PADDR(desc_body_idx);
            virtq.desc[desc_body_idx].len = sizeof(struct virtio_gpu_mem_entry);

            struct virtio_gpu_mem_entry *mem_entry = (struct virtio_gpu_mem_entry *)VIRTIO_DATA(desc_body_idx);
            mem_entry->addr = req.resource_attach_backing.mem_offset + gpu_client_data_paddr;
            mem_entry->length = req.resource_attach_backing.mem_size;

            virtq.desc[desc_body_idx].next = desc_footer_idx;
            virtq.desc[desc_body_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            break;
        }
        case GPU_REQ_RESOURCE_DETACH_BACKING: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_RESOURCE_DETACH_BACKING;
            struct virtio_gpu_resource_detach_backing *resource_detach_backing =
                (struct virtio_gpu_resource_detach_backing *)VIRTIO_DATA(desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_resource_detach_backing);
            resource_detach_backing->hdr.type = VIRTIO_GPU_CMD_RESOURCE_DETACH_BACKING;
            resource_detach_backing->hdr.flags = VIRTIO_GPU_FLAG_FENCE;
            resource_detach_backing->hdr.fence_id = 0;
            resource_detach_backing->resource_id = req.resource_detach_backing.resource_id;

            virtq.desc[desc_head_idx].next = desc_footer_idx;
            virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            break;
        }
        case GPU_REQ_SET_SCANOUT: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_SET_SCANOUT;
            struct virtio_gpu_set_scanout *set_scanout = (struct virtio_gpu_set_scanout *)VIRTIO_DATA(desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_set_scanout);
            set_scanout->hdr.type = VIRTIO_GPU_CMD_SET_SCANOUT;
            set_scanout->hdr.flags = VIRTIO_GPU_FLAG_FENCE;
            set_scanout->hdr.fence_id = 0;
            set_scanout->resource_id = req.set_scanout.resource_id;
            set_scanout->scanout_id = req.set_scanout.scanout_id;
            set_scanout->r.x = req.set_scanout.rect.x;
            set_scanout->r.y = req.set_scanout.rect.y;
            set_scanout->r.width = req.set_scanout.rect.width;
            set_scanout->r.height = req.set_scanout.rect.height;
            virtq.desc[desc_head_idx].next = desc_footer_idx;
            virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            break;
        }
        case GPU_REQ_TRANSFER_TO_2D: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_TRANSFER_TO_HOST_2D;
            struct virtio_gpu_transfer_to_host_2d *transfer_to_2d =
                (struct virtio_gpu_transfer_to_host_2d *)VIRTIO_DATA(desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_transfer_to_host_2d);
            transfer_to_2d->hdr.type = VIRTIO_GPU_CMD_TRANSFER_TO_HOST_2D;
            transfer_to_2d->hdr.flags = VIRTIO_GPU_FLAG_FENCE;
            transfer_to_2d->hdr.fence_id = 0;
            transfer_to_2d->offset = req.transfer_to_2d.mem_offset;
            transfer_to_2d->resource_id = req.transfer_to_2d.resource_id;
            transfer_to_2d->r.x = req.transfer_to_2d.rect.x;
            transfer_to_2d->r.y = req.transfer_to_2d.rect.y;
            transfer_to_2d->r.width = req.transfer_to_2d.rect.width;
            transfer_to_2d->r.height = req.transfer_to_2d.rect.height;

            virtq.desc[desc_head_idx].next = desc_footer_idx;
            virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            break;
        }
        case GPU_REQ_RESOURCE_FLUSH: {
            reqsbk[req.id].virtio_code = VIRTIO_GPU_CMD_RESOURCE_FLUSH;
            struct virtio_gpu_resource_flush *resource_flush = (struct virtio_gpu_resource_flush *)VIRTIO_DATA(
                                                                   desc_head_idx);
            virtq.desc[desc_head_idx].len = sizeof(struct virtio_gpu_resource_flush);
            resource_flush->hdr.type = VIRTIO_GPU_CMD_RESOURCE_FLUSH;
            resource_flush->hdr.flags = VIRTIO_GPU_FLAG_FENCE;
            resource_flush->hdr.fence_id = 0;
            resource_flush->resource_id = req.resource_flush.resource_id;
            resource_flush->r.x = req.resource_flush.rect.x;
            resource_flush->r.y = req.resource_flush.rect.y;
            resource_flush->r.width = req.resource_flush.rect.width;
            resource_flush->r.height = req.resource_flush.rect.height;

            virtq.desc[desc_head_idx].next = desc_footer_idx;
            virtq.desc[desc_head_idx].flags = VIRTQ_DESC_F_NEXT;

            virtq.desc[desc_footer_idx].len = sizeof(struct virtio_gpu_ctrl_hdr);
            break;
        }
        default: {
            /* Received an sDDF gpu request code we don't recognise. Since the virtualiser has already
             * sanitised all bad requests, this means the driver has received a valid sddf request code
             * but that it does not support.
             * Now we respond unspecified error to unsupported request, but first we need to undo all changed states and
             * free all allocated resources.
             */
            LOG_GPU_VIRTIO_DRIVER_ERR("Unsupported sddf request code %d, failing request\n", req.code);
            err = ialloc_free(&ialloc_desc, desc_head_idx);
            assert(!err);
            err = ialloc_free(&ialloc_desc, desc_footer_idx);
            assert(!err);
            virtq.avail->idx--;

            if (gpu_queue_full_resp(&gpu_queue_h)) {
                LOG_GPU_VIRTIO_DRIVER_ERR("Response queue is full, dropping response\n");
                continue;
            }

            err = gpu_enqueue_resp(&gpu_queue_h, (gpu_resp_t) {
                req.id, GPU_RESP_ERR_UNSPEC
            });
            assert(!err);
            sddf_notify = true;
            break;
        }
        }
        virtio_queue_notify = true;
    }

    if (sddf_notify) {
        microkit_notify(VIRT_CH);
    }

    if (virtio_queue_notify) {
        LOG_GPU_VIRTIO_DRIVER("Notifying device about new queue entries\n");
        regs->QueueNotify = 0;
    }
}

static void handle_irq()
{
    bool notify = false;
    uint32_t irq_status = regs->InterruptStatus;
    if (irq_status & VIRTIO_MMIO_IRQ_VQUEUE) {
        LOG_GPU_VIRTIO_DRIVER("Received virtqueue used buffer notification\n");
        notify = handle_response();
        regs->InterruptACK = VIRTIO_MMIO_IRQ_VQUEUE;
        /* Now that there are (maybe) some free descriptors, we want to handle any remaining
         * requests that we may have left in the queue before due to being
         * out of free descriptors.
         */
        handle_request();
    }

    if (irq_status & VIRTIO_MMIO_IRQ_CONFIG) {
        if (virtio_config->events_read & VIRTIO_GPU_EVENT_DISPLAY) {
            LOG_GPU_VIRTIO_DRIVER("Received display info event\n");
            gpu_events_set_display_info(gpu_events);
            virtio_config->events_clear = VIRTIO_GPU_EVENT_DISPLAY;
            regs->InterruptACK = VIRTIO_MMIO_IRQ_CONFIG;
            notify = true;
        } else {
            LOG_GPU_VIRTIO_DRIVER_ERR("Unknown event: 0x%x\n", virtio_config->events_read);
        }
    }

    if (notify) {
        microkit_notify(VIRT_CH);
    } else {
        LOG_GPU_VIRTIO_DRIVER_ERR("Received interrupt but is neither a used buffer notification nor "
                                  "a gpu event, irq status: 0x%x\n",
                                  irq_status);
    }
}
