/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stddef.h>
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/gpu/queue.h>
#include <sddf/gpu/events.h>
#include <sddf/timer/client.h>
#include <gpu_config.h>

/* Uncomment this to enable debug logging */
#define DEBUG_GPU_CLIENT

#if defined(DEBUG_GPU_CLIENT)
#define LOG_GPU_CLIENT(...) do{ sddf_dprintf("GPU_CLIENT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_GPU_CLIENT(...) do{}while(0)
#endif
#define LOG_GPU_CLIENT_ERR(...) do{ sddf_dprintf("GPU_CLIENT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

#define VIRT_CH 0
#define TIMER_CH 1

#define DISPLAY_INFO_DATA_OFFSET 0x1000

#ifndef FB_IMG_WIDTH
#error "FB_IMG_WIDTH not defined"
#endif
#ifndef FB_IMG_HEIGHT
#error "FB_IMG_HEIGHT not defined"
#endif

_Static_assert(FB_IMG_WIDTH *FB_IMG_HEIGHT * GPU_BPP_2D <= GPU_DATA_REGION_SIZE_CLI0 - DISPLAY_INFO_DATA_OFFSET,
               "FB_IMG_WIDTH * FB_IMG_HEIGHT * GPU_BPP_2D must be less than or "
               "equal to GPU_VIRTIO_DATA_REGION_SIZE");

gpu_events_t *gpu_events;
gpu_req_queue_t *gpu_req_queue;
gpu_resp_queue_t *gpu_resp_queue;
uintptr_t gpu_data;

extern char _fb_img[];
extern char _fb_img_end[];

static gpu_queue_handle_t gpu_queue_handle;
static uint32_t req_id = 0;
static uint32_t display_info_req_id = -1;
static gpu_resp_get_display_info_t display_info = { 0 };
static bool display_info_init = false;
static bool pending_display_info_request = false;

enum draw_state {
    DRAW_FULL,
    DRAW_QUADRANT,
    DRAW_DISABLE,
#ifdef GPU_BLOB_SUPPORT
    DRAW_FULL_BLOB,
    DRAW_QUADRANT_BLOB,
    DRAW_DISABLE_BLOB,
#endif
} draw_state = DRAW_FULL;

static int get_and_inc_req_id(void)
{
    int ret = req_id;
    req_id++;
    return ret;
}

#ifdef GPU_BLOB_SUPPORT
static void draw_image_blob(int resource_id, int res_width, int res_height, gpu_rect_t rect)
{
    int err = 0;
    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_RESOURCE_CREATE_BLOB,
        .id = get_and_inc_req_id(),
        .resource_create_blob = {
            .resource_id = resource_id,
            .mem_offset = DISPLAY_INFO_DATA_OFFSET,
            .mem_size = res_width * res_height * GPU_BPP_2D,
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_SET_SCANOUT_BLOB,
        .id = get_and_inc_req_id(),
        .set_scanout_blob = {
            .resource_id = resource_id,
            .scanout_id = 0,
            .rect.x = rect.x,
            .rect.y = rect.y,
            .rect.width = rect.width,
            .rect.height = rect.height,
            .format = GPU_FORMAT_B8G8R8A8_UNORM,
            .width = res_width,
            .height = res_height,
            .offset = 0,
            .stride = res_width * GPU_BPP_2D,
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_RESOURCE_FLUSH,
        .id = get_and_inc_req_id(),
        .resource_flush = {
            .resource_id = resource_id,
            .rect.x = rect.x,
            .rect.y = rect.y,
            .rect.width = rect.width,
            .rect.height = rect.height,
        },
    });
    assert(!err);

    LOG_GPU_CLIENT("Drawing blob image! Making the following requests:\n\
    resource_create_blob: mem_offset: %d mem_size: %d\n\
    set_scanout_blob: rect.x: %d rect.y: %d rect.width: %d rect.height: %d scanout_id: %d, format: %d\n\
                      width: %d height: %d offset: %d stride: %d\n\
    resource_flush: rect.x: %d rect.y: %d rect.width: %d rect.height: %d\n",
                   DISPLAY_INFO_DATA_OFFSET, res_width * res_height * GPU_BPP_2D, rect.x, rect.y, rect.width,
                   rect.height, 0, GPU_FORMAT_B8G8R8A8_UNORM, res_width, res_height, 0, res_width * GPU_BPP_2D, rect.x,
                   rect.y, rect.width, rect.height);
}
#endif

static void draw_image(int resource_id, int res_width, int res_height, int xfer_offset, gpu_rect_t rect)
{
    int err = 0;
    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_RESOURCE_CREATE_2D,
        .id = get_and_inc_req_id(),
        .resource_create_2d = {
            .resource_id = resource_id,
            .width = res_width,
            .height = res_height,
            .format = GPU_FORMAT_B8G8R8A8_UNORM,
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_RESOURCE_ATTACH_BACKING,
        .id = get_and_inc_req_id(),
        .resource_attach_backing = {
            .resource_id = resource_id,
            .mem_offset = DISPLAY_INFO_DATA_OFFSET,
            .mem_size = res_width * res_height * GPU_BPP_2D,
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_SET_SCANOUT,
        .id = get_and_inc_req_id(),
        .set_scanout = {
            .resource_id = resource_id,
            .scanout_id = 0,
            .rect.x = rect.x,
            .rect.y = rect.y,
            .rect.width = rect.width,
            .rect.height = rect.height,
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_TRANSFER_TO_2D,
        .id = get_and_inc_req_id(),
        .transfer_to_2d = {
            .resource_id = resource_id,
            .rect.x = rect.x,
            .rect.y = rect.y,
            .rect.width = rect.width,
            .rect.height = rect.height,
            .mem_offset = xfer_offset,
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_RESOURCE_FLUSH,
        .id = get_and_inc_req_id(),
        .resource_flush = {
            .resource_id = resource_id,
            .rect.x = rect.x,
            .rect.y = rect.y,
            .rect.width = rect.width,
            .rect.height = rect.height,
        },
    });
    assert(!err);

    LOG_GPU_CLIENT("Drawing image! Making the following requests:\n\
    resource_create_2d: width: %d height: %d format: bgra\n\
    attach_backing: mem_offset: %d mem_size: %d\n\
    set_scanout: scanout_id: 0 rect.x: %d rect.y: %d rect.width: %d rect.height: %d\n\
    transfer_to_2d: rect.x: %d rect.y: %d rect.width: %d rect.height: %d mem_offset: %d\n\
    resource_flush: rect.x: %d rect.y: %d rect.width: %d rect.height: %d\n",
                   res_width, res_height, 0x1000 + (FB_IMG_WIDTH * FB_IMG_HEIGHT * GPU_BPP_2D), res_width * res_height,
                   rect.x, rect.y, rect.width, rect.height, rect.x, rect.y, rect.width, rect.height, xfer_offset,
                   rect.x, rect.y, rect.width, rect.height);
}

static void cleanup_resources(int resource_id_1, int resource_id_2)
{
    int err = 0;
    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_SET_SCANOUT,
        .id = get_and_inc_req_id(),
        .set_scanout = {
            .resource_id = 0,
            .scanout_id = 0,
            .rect = {
                .x = 0,
                .y = 0,
                .width = 0,
                .height = 0,
            },
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_RESOURCE_DETACH_BACKING,
        .id = get_and_inc_req_id(),
        .resource_detach_backing = {
            .resource_id = resource_id_1,
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_RESOURCE_DETACH_BACKING,
        .id = get_and_inc_req_id(),
        .resource_detach_backing = {
            .resource_id = resource_id_2,
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_RESOURCE_UNREF,
        .id = get_and_inc_req_id(),
        .resource_unref = {
            .resource_id = resource_id_1,
        },
    });
    assert(!err);

    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_RESOURCE_UNREF,
        .id = get_and_inc_req_id(),
        .resource_unref = {
            .resource_id = resource_id_2,
        },
    });
    assert(!err);
}

static void do_draw_state(void)
{
    switch (draw_state) {
    case DRAW_FULL:
        /* This will make the following requests:
         * 1. Create a 2D resource with the image width and height
         * 2. Attach the image to the resource as memory backing
         * 3. Set the scanout to the resource with its full size
         * 4. Transfer the full resource to the other side
         * 5. Flush the full resource to the scanout
         */
        draw_image(1, FB_IMG_WIDTH, FB_IMG_HEIGHT, 0,
        (gpu_rect_t) {
            .x = 0,
            .y = 0,
            .width = FB_IMG_WIDTH,
            .height = FB_IMG_HEIGHT,
        });
        sddf_timer_set_timeout(TIMER_CH, NS_IN_S);
        draw_state = DRAW_QUADRANT;
        microkit_notify(VIRT_CH);
        break;
    case DRAW_QUADRANT:
        /* This will make the following requests:
         * 1. Create a 2D resource with the image width and height
         * 2. Attach the image to the resource as memory backing
         *    (both resources now have the same memory backing)
         * 3. Set the scanout to the bottom right quadrant of the resource
         * 4. Transfer to the resource from the top right quadrant to the bottom right quadrant
         * 5. Flush the bottom right quadrant of the resource to the scanout
         */
        draw_image(2, FB_IMG_WIDTH, FB_IMG_HEIGHT, FB_IMG_WIDTH / 2 * GPU_BPP_2D,
        (gpu_rect_t) {
            .x = FB_IMG_WIDTH / 2,
            .y = FB_IMG_HEIGHT / 2,
            .width = FB_IMG_WIDTH / 2,
            .height = FB_IMG_HEIGHT / 2,
        });
        sddf_timer_set_timeout(TIMER_CH, NS_IN_S);
        draw_state = DRAW_DISABLE;
        microkit_notify(VIRT_CH);
        break;
    case DRAW_DISABLE:
        /* This will make the following requests:
         * 1. Disable the scanout
         * 2. Detach the memory backing of the two resources
         * 3. Destroy the two resources
         */
        cleanup_resources(1, 2);
        sddf_timer_set_timeout(TIMER_CH, NS_IN_S);
#ifdef GPU_BLOB_SUPPORT
        draw_state = DRAW_FULL_BLOB;
#else
        draw_state = DRAW_FULL;
#endif
        microkit_notify(VIRT_CH);
        break;
#ifdef GPU_BLOB_SUPPORT
    case DRAW_FULL_BLOB:
        /* This will make the following requests:
         * 1. Create a blob resource with the image width and height
         * 2. Set the scanout to the blob with its full size
         * 3. Flush the full blob to the scanout
         */
        draw_image_blob(1, FB_IMG_WIDTH, FB_IMG_HEIGHT,
        (gpu_rect_t) {
            .x = 0,
            .y = 0,
            .width = FB_IMG_WIDTH,
            .height = FB_IMG_HEIGHT,
        });
        sddf_timer_set_timeout(TIMER_CH, NS_IN_S);
        draw_state = DRAW_QUADRANT_BLOB;
        microkit_notify(VIRT_CH);
        break;
    case DRAW_QUADRANT_BLOB:
        /* This will make the following requests:
         * 1. Set the scanout to the bottom right quadrant of the blob
         * 2. Flush the bottom right quadrant of the blob to the scanout
         */
        draw_image_blob(2, FB_IMG_WIDTH, FB_IMG_HEIGHT,
        (gpu_rect_t) {
            .x = FB_IMG_WIDTH / 2,
            .y = FB_IMG_HEIGHT / 2,
            .width = FB_IMG_WIDTH / 2,
            .height = FB_IMG_HEIGHT / 2,
        });
        sddf_timer_set_timeout(TIMER_CH, NS_IN_S);
        draw_state = DRAW_DISABLE_BLOB;
        microkit_notify(VIRT_CH);
        break;
    case DRAW_DISABLE_BLOB:
        /* This will make the following requests:
         * 1. Disable the scanout
         * 2. Destroy the two blob resources
         */
        cleanup_resources(1, 2);
        sddf_timer_set_timeout(TIMER_CH, NS_IN_S);
        draw_state = DRAW_FULL;
        microkit_notify(VIRT_CH);
        break;
#endif
    }
}

static void handle_display_info_response()
{
    sddf_memcpy(&display_info, (void *)(gpu_data), sizeof(gpu_resp_get_display_info_t));
    LOG_GPU_CLIENT("Display info received: num_scanouts=%d\n", display_info.num_scanouts);
    for (int i = 0; i < display_info.num_scanouts; i++) {
        LOG_GPU_CLIENT("Scanout %d: enabled=%d, rect=(%d, %d, %d, %d) {x, y, "
                       "width, height}\n",
                       i, display_info.scanouts[i].enabled, display_info.scanouts[i].rect.x,
                       display_info.scanouts[i].rect.y, display_info.scanouts[i].rect.width,
                       display_info.scanouts[i].rect.height);
    }
}

static void request_display_info()
{
    int err = 0;
    display_info_req_id = get_and_inc_req_id();
    err = gpu_enqueue_req(&gpu_queue_handle, (gpu_req_t) {
        .code = GPU_REQ_GET_DISPLAY_INFO,
        .id = display_info_req_id,
        .get_display_info = {
            .mem_offset = 0,
        },
    });
    assert(!err);
}

void init(void)
{
    LOG_GPU_CLIENT("Initialising GPU client!\n");
    /* Assert image size does not exceed data region size */
    assert(FB_IMG_WIDTH * FB_IMG_HEIGHT * GPU_BPP_2D + DISPLAY_INFO_DATA_OFFSET <= GPU_DATA_REGION_SIZE_CLI0);
    gpu_queue_init(&gpu_queue_handle, gpu_req_queue, gpu_resp_queue, GPU_QUEUE_CAPACITY_CLI0);
    sddf_memcpy((void *)(gpu_data + 0x1000), (void *)_fb_img, (size_t)(_fb_img_end - _fb_img));

    /* As part of initialisation, request for display info before sending anything else */
    LOG_GPU_CLIENT("Requesting initial display info\n");
    request_display_info();
    microkit_notify(VIRT_CH);
}

void notified(microkit_channel ch)
{
    int err = 0;
    if (!display_info_init) {
        if (ch == VIRT_CH) {
            gpu_resp_t resp = { 0 };
            err = gpu_dequeue_resp(&gpu_queue_handle, &resp);
            assert(!err);
            assert(resp.id == display_info_req_id);
            LOG_GPU_CLIENT("Initialised display info\n");
            handle_display_info_response();
            assert(display_info.num_scanouts > 0);
            assert(display_info.scanouts[0].enabled);
            display_info_init = true;
            LOG_GPU_CLIENT("Now starting the draw state machine\n");
            do_draw_state();
        }
        return;
    }

    if (ch == TIMER_CH) {
        LOG_GPU_CLIENT("Received notification from timer\n");
        do_draw_state();
        return;
    }

    LOG_GPU_CLIENT("Received notification from virtualiser\n");

    if (gpu_events_check_display_info(gpu_events) && !pending_display_info_request) {
        gpu_events_clear_display_info(gpu_events);
        LOG_GPU_CLIENT("Display info event received\n");
        LOG_GPU_CLIENT("Requesting display info\n");
        request_display_info();
        pending_display_info_request = true;
        microkit_notify(VIRT_CH);
        return;
    }

    gpu_resp_t resp = { 0 };
    while (!gpu_queue_empty_resp(&gpu_queue_handle)) {
        err = gpu_dequeue_resp(&gpu_queue_handle, &resp);
        assert(!err);
        if (resp.status != GPU_RESP_OK) {
            LOG_GPU_CLIENT_ERR("Failed request %d with status %d\n", resp.id, resp.status);
        }
        assert(resp.status == GPU_RESP_OK);
        LOG_GPU_CLIENT("Response received for request %d\n", resp.id);
        if (resp.id == display_info_req_id) {
            handle_display_info_response();
            pending_display_info_request = false;
        }
    }
}
