/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/gpu/queue.h>
#include <sddf/gpu/events.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>
#include <sddf/util/cache.h>
#include <gpu_config.h>

/* Uncomment this to enable debug logging */
#define DEBUG_GPU_VIRT

#if defined(DEBUG_GPU_VIRT)
#define LOG_GPU_VIRT(...) do{ sddf_dprintf("GPU_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_GPU_VIRT(...) do{}while(0)
#endif
#define LOG_GPU_VIRT_ERR(...) do{ sddf_dprintf("GPU_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

#define DRIVER_CH 0
#define CLI_CH_OFFSET 1

#define UNMAPPED_RESOURCE_ID UINT32_MAX
_Static_assert(
    GPU_MAX_RESOURCES <= UINT32_MAX - 2,
    "Resource ids can only occupy 32 bits of memory, with the smallest value of 0 reserved for disabling scanout and\
the largest value reserved for unmapped resources");

#define VIRTUALISER_ID UINT32_MAX
_Static_assert(GPU_NUM_CLIENTS <= UINT32_MAX - 1, "Client ids can only occupy 32 bits of memory, with the largest "
               "value reserved for virtualiser id itself");

/* Microkit patched variables */
gpu_events_t *gpu_driver_events;
gpu_req_queue_t *gpu_driver_req_queue;
gpu_resp_queue_t *gpu_driver_resp_queue;
uintptr_t gpu_driver_data;
gpu_events_t *gpu_client_events;
gpu_req_queue_t *gpu_client_req_queue;
gpu_resp_queue_t *gpu_client_resp_queue;
uintptr_t gpu_client_data;

gpu_queue_handle_t drv_h;

typedef struct client {
    gpu_queue_handle_t queue_h;
    gpu_events_t *events;
    microkit_channel ch;
    /* Mapping from virtualiser resource id to driver resource id */
    uint32_t res_map_virt_to_drv[GPU_MAX_RESOURCES + 1];
} client_t;
static client_t clients[GPU_NUM_CLIENTS];
/* Driver resource id allocations */
static ialloc_t res_ialloc;
static uint32_t res_ialloc_idxlist[GPU_MAX_RESOURCES];

typedef struct resource {
    bool has_backing;
    uint32_t width;
    uint32_t height;
    bool is_blob;
    uint64_t mem_offset;
    uint32_t mem_size;
} resource_t;
/* Indexed by driver resource id */
static resource_t drv_resources[GPU_MAX_RESOURCES + 1];

typedef struct blob_scanout {
    bool active;
    uint32_t width;
    uint32_t height;
} blob_scanout_t;
/* Indexed by resource id and scanout id */
static blob_scanout_t blob_scanouts[GPU_MAX_SCANOUTS][GPU_MAX_RESOURCES + 1];

/* This bookkeeping exists to store information between a request/response pair. */
typedef struct reqbk {
    uint32_t cli_id;
    uint32_t cli_req_id;
    gpu_req_code_t code;
    uint32_t res_virt;
    uint32_t res_scanout;
} reqbk_t;
/* Indexed by virt-to-drv request id */
static reqbk_t reqsbk[GPU_QUEUE_CAPACITY_DRV];
/* Virt-to-drv request id allocations */
static ialloc_t req_ialloc;
static uint32_t req_ialloc_idxlist[GPU_QUEUE_CAPACITY_DRV];

/* Display info populated during initialisation and any display_info event */
static gpu_resp_get_display_info_t get_display_info = { 0 };

static bool pending_display_info_request = false;
static bool try_again_display_info_req = false;
static bool display_info_init = false;

static void handle_clients(void);
static void handle_driver(void);
static void init_request_get_display_info(void);
static bool handle_init_get_display_info_response(void);

void init(void)
{
    LOG_GPU_VIRT("Initialising GPU virtualiser!\n");
    ialloc_init(&req_ialloc, req_ialloc_idxlist, GPU_QUEUE_CAPACITY_DRV);
    ialloc_init_with_offset(&res_ialloc, res_ialloc_idxlist, GPU_MAX_RESOURCES, 1);

    /* Initialise client queues */
    for (int i = 0; i < GPU_NUM_CLIENTS; i++) {
        gpu_req_queue_t *curr_req = gpu_virt_cli_req_queue(gpu_client_req_queue, i);
        gpu_resp_queue_t *curr_resp = gpu_virt_cli_resp_queue(gpu_client_resp_queue, i);
        uint32_t curr_queue_capacity = gpu_virt_cli_queue_capacity(i);
        gpu_queue_init(&clients[i].queue_h, curr_req, curr_resp, curr_queue_capacity);
        gpu_events_t *curr_events = gpu_virt_cli_events_region(gpu_client_events, i);
        clients[i].events = curr_events;
        clients[i].ch = CLI_CH_OFFSET + i;
        for (int j = 1; j < GPU_MAX_RESOURCES + 1; j++) {
            clients[i].res_map_virt_to_drv[j] = UNMAPPED_RESOURCE_ID;
        }
    }

    gpu_queue_init(&drv_h, gpu_driver_req_queue, gpu_driver_resp_queue, GPU_QUEUE_CAPACITY_DRV);
    LOG_GPU_VIRT("Requesting initial display info\n");
    init_request_get_display_info();
}

void notified(microkit_channel ch)
{
#ifdef DEBUG_GPU_VIRT
    if (ch == DRIVER_CH) {
        LOG_GPU_VIRT("Received notification from driver\n");
    } else {
        int cli_id = ch - CLI_CH_OFFSET;
        LOG_GPU_VIRT("Received notification from client %d\n", cli_id);
    }
#endif
    if (!display_info_init) {
        if (ch == DRIVER_CH && handle_init_get_display_info_response()) {
            display_info_init = true;
            LOG_GPU_VIRT("Initialised display info\n");
        } else {
            return;
        }
    }

    if (ch == DRIVER_CH) {
        handle_driver();
        handle_clients();
    } else {
        handle_clients();
    }
}

static inline void init_request_get_display_info()
{
    int err = 0;
    err = gpu_enqueue_req(&drv_h, (gpu_req_t) {
        .code = GPU_REQ_GET_DISPLAY_INFO,
        .id = 0,
        .get_display_info = {
            .mem_offset = 0,
        },
    });
    assert(!err);
    microkit_notify(DRIVER_CH);
}

static inline bool handle_init_get_display_info_response()
{
    int err = 0;
    if (gpu_queue_empty_resp(&drv_h)) {
        LOG_GPU_VIRT("Waiting on display info response, but response queue is empty\n");
        return false;
    }
    gpu_resp_t resp = { 0 };
    err = gpu_dequeue_resp(&drv_h, &resp);
    assert(!err);
    assert(resp.id == 0);
    assert(resp.status == GPU_RESP_OK);
    sddf_memcpy(&get_display_info, (void *)gpu_driver_data, sizeof(gpu_resp_get_display_info_t));
    return true;
}

/* True if a rectangle at position rect.x and rect.y with dimensions rect.width and rect.height is contained within the width and height of another rectangle */
static inline bool rect_overlaps(uint32_t width, uint32_t height, gpu_rect_t rect)
{
    return rect.x + rect.width <= width && rect.y + rect.height <= height;
}

#ifdef GPU_BLOB_SUPPORT
static inline bool gpu_resource_create_blob(int cli_id, gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (req->resource_create_blob.resource_id == GPU_DISABLE_SCANOUT_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("RESOURCE_CREATE_BLOB: Cannot create resource on "
                         "reserved resource id, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (clients[cli_id].res_map_virt_to_drv[req->resource_create_blob.resource_id] != UNMAPPED_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("RESOURCE_CREATE_BLOB: Resource already exists, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (ialloc_full(&res_ialloc)) {
        LOG_GPU_VIRT_ERR("RESOURCE_CREATE_BLOB: Resource mapping is full, "
                         "failing request\n");
        fail_resp->status = GPU_RESP_ERR_UNSPEC;
        return false;
    }

    if (req->resource_create_blob.mem_offset + req->resource_create_blob.mem_size
        > gpu_virt_cli_data_region_size(cli_id)) {
        LOG_GPU_VIRT_ERR("RESOURCE_CREATE_BLOB: Range in memory region to store blob "
                         "resource is out of its allocated bounds, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_PARAMETER;
        return false;
    }

    uint32_t drv_res_id = 0;
    int err = ialloc_alloc(&res_ialloc, &drv_res_id);
    assert(!err);
    clients[cli_id].res_map_virt_to_drv[req->resource_create_blob.resource_id] = drv_res_id;
    drv_resources[drv_res_id].is_blob = true;
    drv_resources[drv_res_id].has_backing = true;
    drv_resources[drv_res_id].mem_offset = req->resource_create_blob.mem_offset;
    drv_resources[drv_res_id].mem_size = req->resource_create_blob.mem_size;
    /* Not used for blob resources */
    drv_resources[drv_res_id].width = 0;
    drv_resources[drv_res_id].height = 0;

    reqsbk[drv_req->id].res_virt = req->resource_create_blob.resource_id;

    drv_req->code = GPU_REQ_RESOURCE_CREATE_BLOB;
    drv_req->resource_create_blob.resource_id = drv_res_id;
    drv_req->resource_create_blob.mem_offset = req->resource_create_blob.mem_offset;
    drv_req->resource_create_blob.mem_size = req->resource_create_blob.mem_size;
    return true;
}

static inline bool gpu_set_scanout_blob(int cli_id, gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (req->set_scanout_blob.scanout_id >= GPU_MAX_SCANOUTS) {
        LOG_GPU_VIRT_ERR("SET_SCANOUT_BLOB: Scanout id invalid, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_SCANOUT_ID;
        return false;
    }

    /* Disable scanout case */
    if (req->set_scanout_blob.resource_id == GPU_DISABLE_SCANOUT_RESOURCE_ID) {
        for (int i = 0; i < GPU_MAX_RESOURCES + 1; i++) {
            blob_scanouts[req->set_scanout_blob.scanout_id][i].active = false;
        }
        reqsbk[drv_req->id].res_virt = req->set_scanout_blob.resource_id;
        drv_req->code = GPU_REQ_SET_SCANOUT_BLOB;
        drv_req->set_scanout_blob.resource_id = GPU_DISABLE_SCANOUT_RESOURCE_ID;
        drv_req->set_scanout_blob.scanout_id = req->set_scanout_blob.scanout_id;
        return true;
    }

    if (clients[cli_id].res_map_virt_to_drv[req->set_scanout_blob.resource_id] == UNMAPPED_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("SET_SCANOUT_BLOB: Resource id invalid, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (!drv_resources[clients[cli_id].res_map_virt_to_drv[req->set_scanout_blob.resource_id]].is_blob) {
        LOG_GPU_VIRT_ERR("SET_SCANOUT_BLOB: Resource is not a blob resource, "
                         "failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (req->set_scanout_blob.offset + req->set_scanout_blob.stride * req->set_scanout_blob.height
        > drv_resources[clients[cli_id].res_map_virt_to_drv[req->set_scanout_blob.resource_id]].mem_size) {
        LOG_GPU_VIRT_ERR("SET_SCANOUT_BLOB: Specified resource memory layout "
                         "exceeds its allocated memory, failing request\n");
        fail_resp->status = GPU_RESP_ERR_UNSPEC;
        return false;
    }

    if (!rect_overlaps(req->set_scanout_blob.width, req->set_scanout_blob.height, req->set_scanout_blob.rect)) {
        LOG_GPU_VIRT_ERR("SET_SCANOUT_BLOB: Scanout rectangle is outside the "
                         "bounds of the resource, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_BOUNDS;
        return false;
    }

    blob_scanouts[req->set_scanout_blob.scanout_id][req->set_scanout_blob.resource_id].active = true;
    blob_scanouts[req->set_scanout_blob.scanout_id][req->set_scanout_blob.resource_id].width =
        req->set_scanout_blob.width;
    blob_scanouts[req->set_scanout_blob.scanout_id][req->set_scanout_blob.resource_id].height =
        req->set_scanout_blob.height;

    reqsbk[drv_req->id].res_virt = req->set_scanout_blob.resource_id;

    drv_req->code = GPU_REQ_SET_SCANOUT_BLOB;
    drv_req->set_scanout_blob.resource_id = clients[cli_id].res_map_virt_to_drv[req->set_scanout_blob.resource_id];
    /* Give each client the same view of scanouts as virtualiser */
    drv_req->set_scanout_blob.scanout_id = req->set_scanout_blob.scanout_id;
    drv_req->set_scanout_blob.rect = req->set_scanout_blob.rect;
    drv_req->set_scanout_blob.offset = req->set_scanout_blob.offset;
    drv_req->set_scanout_blob.stride = req->set_scanout_blob.stride;
    drv_req->set_scanout_blob.width = req->set_scanout_blob.width;
    drv_req->set_scanout_blob.height = req->set_scanout_blob.height;
    return true;
}
#endif

static inline bool gpu_resource_create_2d(int cli_id, gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    int err = 0;
    if (req->resource_create_2d.resource_id == GPU_DISABLE_SCANOUT_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("RESOURCE_CREATE_2D: Cannot create resource on "
                         "reserved resource id, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (clients[cli_id].res_map_virt_to_drv[req->resource_create_2d.resource_id] != UNMAPPED_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("RESOURCE_CREATE_2D: Resource already exists, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (ialloc_full(&res_ialloc)) {
        LOG_GPU_VIRT_ERR("RESOURCE_CREATE_2D: Resource mapping is full, failing request\n");
        fail_resp->status = GPU_RESP_ERR_UNSPEC;
        return false;
    }

    uint32_t drv_res_id = 0;
    err = ialloc_alloc(&res_ialloc, &drv_res_id);
    assert(!err);
    clients[cli_id].res_map_virt_to_drv[req->resource_create_2d.resource_id] = drv_res_id;
    drv_resources[drv_res_id].width = req->resource_create_2d.width;
    drv_resources[drv_res_id].height = req->resource_create_2d.height;
    drv_resources[drv_res_id].has_backing = false;
    drv_resources[drv_res_id].is_blob = false;
    /* Not used for regular resources */
    drv_resources[drv_res_id].mem_offset = 0;
    drv_resources[drv_res_id].mem_size = 0;

    reqsbk[drv_req->id].res_virt = req->resource_create_2d.resource_id;

    drv_req->code = GPU_REQ_RESOURCE_CREATE_2D;
    drv_req->resource_create_2d.resource_id = drv_res_id;
    drv_req->resource_create_2d.width = req->resource_create_2d.width;
    drv_req->resource_create_2d.height = req->resource_create_2d.height;
    drv_req->resource_create_2d.format = req->resource_create_2d.format;
    return true;
}

static inline bool gpu_resource_unref(int cli_id, gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    int err = 0;
    if (req->resource_unref.resource_id == GPU_DISABLE_SCANOUT_RESOURCE_ID
        || clients[cli_id].res_map_virt_to_drv[req->resource_unref.resource_id] == UNMAPPED_RESOURCE_ID) {
        LOG_GPU_VIRT("RESOURCE_UNREF: Resource id invalid, failing request");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_unref.resource_id]].is_blob) {
        for (int i = 0; i < GPU_MAX_SCANOUTS; i++) {
            blob_scanouts[i][clients[cli_id].res_map_virt_to_drv[req->resource_unref.resource_id]].active = false;
        }
    }

    reqsbk[drv_req->id].res_virt = req->resource_unref.resource_id;

    drv_req->code = GPU_REQ_RESOURCE_UNREF;
    drv_req->resource_unref.resource_id = clients[cli_id].res_map_virt_to_drv[req->resource_unref.resource_id];
    err = ialloc_free(&res_ialloc, clients[cli_id].res_map_virt_to_drv[req->resource_unref.resource_id]);
    assert(!err);
    clients[cli_id].res_map_virt_to_drv[req->resource_unref.resource_id] = UNMAPPED_RESOURCE_ID;
    return true;
}

static inline bool gpu_resource_attach_backing(int cli_id, gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (req->resource_attach_backing.resource_id == GPU_DISABLE_SCANOUT_RESOURCE_ID
        || clients[cli_id].res_map_virt_to_drv[req->resource_attach_backing.resource_id] == UNMAPPED_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("RESOURCE_ATTACH_BACKING: Resource id invalid, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (req->resource_attach_backing.mem_offset + req->resource_attach_backing.mem_size
        > gpu_virt_cli_data_region_size(cli_id)) {
        LOG_GPU_VIRT_ERR("RESOURCE_ATTACH_BACKING: Range in memory region to attach for "
                         "backing is out of its allocated bounds, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_PARAMETER;
        return false;
    }

    if (drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_attach_backing.resource_id]].has_backing) {
        LOG_GPU_VIRT_ERR("RESOURCE_ATTACH_BACKING: Attaching backing to resource which "
                         "already has memory backing, failing request\n");
        fail_resp->status = GPU_RESP_ERR_UNSPEC;
        return false;
    }

    drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_attach_backing.resource_id]].has_backing = true;
    drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_attach_backing.resource_id]].mem_offset =
        req->resource_attach_backing.mem_offset;
    drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_attach_backing.resource_id]].mem_size =
        req->resource_attach_backing.mem_size;

    reqsbk[drv_req->id].res_virt = req->resource_attach_backing.resource_id;

    drv_req->code = GPU_REQ_RESOURCE_ATTACH_BACKING;
    drv_req->resource_attach_backing.resource_id =
        clients[cli_id].res_map_virt_to_drv[req->resource_attach_backing.resource_id];
    drv_req->resource_attach_backing.mem_offset = req->resource_attach_backing.mem_offset;
    drv_req->resource_attach_backing.mem_size = req->resource_attach_backing.mem_size;
    return true;
}

static inline bool gpu_resource_detach_backing(int cli_id, gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (req->resource_detach_backing.resource_id == GPU_DISABLE_SCANOUT_RESOURCE_ID
        || clients[cli_id].res_map_virt_to_drv[req->resource_detach_backing.resource_id] == UNMAPPED_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("RESOURCE_DETACH_BACKING: Resource id invalid, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (!drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_detach_backing.resource_id]].has_backing) {
        LOG_GPU_VIRT_ERR("RESOURCE_DETACH_BACKING: Detaching backing from resource which "
                         "does not have an existing memory backing, failing request\n");
        fail_resp->status = GPU_RESP_ERR_UNSPEC;
        return false;
    }

    drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_detach_backing.resource_id]].has_backing = false;

    reqsbk[drv_req->id].res_virt = req->resource_detach_backing.resource_id;

    drv_req->code = GPU_REQ_RESOURCE_DETACH_BACKING;
    drv_req->resource_detach_backing.resource_id =
        clients[cli_id].res_map_virt_to_drv[req->resource_detach_backing.resource_id];
    return true;
}

static inline bool gpu_set_scanout(int cli_id, gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (req->set_scanout.scanout_id >= GPU_MAX_SCANOUTS) {
        LOG_GPU_VIRT_ERR("SET_SCANOUT: Scanout id invalid, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_SCANOUT_ID;
        return false;
    }

    /* Disable scanout case */
    if (req->set_scanout.resource_id == GPU_DISABLE_SCANOUT_RESOURCE_ID) {
        reqsbk[drv_req->id].res_virt = req->set_scanout.resource_id;
        drv_req->code = GPU_REQ_SET_SCANOUT;
        drv_req->set_scanout.resource_id = GPU_DISABLE_SCANOUT_RESOURCE_ID;
        drv_req->set_scanout.scanout_id = req->set_scanout.scanout_id;
        drv_req->set_scanout.rect.x = 0;
        drv_req->set_scanout.rect.y = 0;
        drv_req->set_scanout.rect.width = 0;
        drv_req->set_scanout.rect.height = 0;
        return true;
    }

    if (clients[cli_id].res_map_virt_to_drv[req->set_scanout.resource_id] == UNMAPPED_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("SET_SCANOUT: Resource id invalid, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (drv_resources[clients[cli_id].res_map_virt_to_drv[req->set_scanout.resource_id]].is_blob) {
        LOG_GPU_VIRT_ERR("SET_SCANOUT: Resource is a blob resource, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (!rect_overlaps(drv_resources[clients[cli_id].res_map_virt_to_drv[req->set_scanout.resource_id]].width,
                       drv_resources[clients[cli_id].res_map_virt_to_drv[req->set_scanout.resource_id]].height,
                       req->set_scanout.rect)) {
        LOG_GPU_VIRT_ERR("SET_SCANOUT: Scanout rectangle out of bounds from "
                         "resource, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_BOUNDS;
        return false;
    }

    reqsbk[drv_req->id].res_virt = req->set_scanout.resource_id;

    drv_req->code = GPU_REQ_SET_SCANOUT;
    drv_req->set_scanout.resource_id = clients[cli_id].res_map_virt_to_drv[req->set_scanout.resource_id];
    /* Give each client the same view of scanouts as virtualiser */
    drv_req->set_scanout.scanout_id = req->set_scanout.scanout_id;
    drv_req->set_scanout.rect.x = req->set_scanout.rect.x;
    drv_req->set_scanout.rect.y = req->set_scanout.rect.y;
    drv_req->set_scanout.rect.width = req->set_scanout.rect.width;
    drv_req->set_scanout.rect.height = req->set_scanout.rect.height;
    return true;
}

static inline bool gpu_transfer_to_2d(int cli_id, gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (req->transfer_to_2d.resource_id == GPU_DISABLE_SCANOUT_RESOURCE_ID
        || clients[cli_id].res_map_virt_to_drv[req->transfer_to_2d.resource_id] == UNMAPPED_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("TRANSFER_TO_2D: Resource id invalid, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (drv_resources[clients[cli_id].res_map_virt_to_drv[req->transfer_to_2d.resource_id]].is_blob) {
        LOG_GPU_VIRT_ERR("TRANSFER_TO_2D: Resource is a blob resource, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (!drv_resources[clients[cli_id].res_map_virt_to_drv[req->transfer_to_2d.resource_id]].has_backing) {
        LOG_GPU_VIRT_ERR("TRANSFER_TO_2D: Resource does not have backing, "
                         "failing request\n");
        fail_resp->status = GPU_RESP_ERR_UNSPEC;
        return false;
    }

    if (!rect_overlaps(drv_resources[clients[cli_id].res_map_virt_to_drv[req->transfer_to_2d.resource_id]].width,
                       drv_resources[clients[cli_id].res_map_virt_to_drv[req->transfer_to_2d.resource_id]].height,
                       req->transfer_to_2d.rect)) {
        LOG_GPU_VIRT_ERR("TRANSFER_TO_2D: Rectangle out of bounds from "
                         "resource, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_BOUNDS;
        return false;
    }

    if (req->transfer_to_2d.mem_offset + req->transfer_to_2d.rect.width * req->transfer_to_2d.rect.height * GPU_BPP_2D
        > drv_resources[clients[cli_id].res_map_virt_to_drv[req->transfer_to_2d.resource_id]].mem_size) {
        LOG_GPU_VIRT_ERR("TRANSFER_TO_2D: Transfer region out of bounds from "
                         "memory backing, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_PARAMETER;
        return false;
    }

    unsigned long transfer_base =
        (unsigned long)(gpu_virt_cli_data_region(gpu_client_data, cli_id)
                        + drv_resources[clients[cli_id].res_map_virt_to_drv[req->transfer_to_2d.resource_id]].mem_offset
                        + req->transfer_to_2d.mem_offset);
    cache_clean(transfer_base,
                transfer_base + req->transfer_to_2d.rect.width * req->transfer_to_2d.rect.height * GPU_BPP_2D);

    reqsbk[drv_req->id].res_virt = req->transfer_to_2d.resource_id;

    drv_req->code = GPU_REQ_TRANSFER_TO_2D;
    drv_req->transfer_to_2d.resource_id = clients[cli_id].res_map_virt_to_drv[req->transfer_to_2d.resource_id];
    drv_req->transfer_to_2d.rect.x = req->transfer_to_2d.rect.x;
    drv_req->transfer_to_2d.rect.y = req->transfer_to_2d.rect.y;
    drv_req->transfer_to_2d.rect.width = req->transfer_to_2d.rect.width;
    drv_req->transfer_to_2d.rect.height = req->transfer_to_2d.rect.height;
    drv_req->transfer_to_2d.mem_offset = req->transfer_to_2d.mem_offset;
    return true;
}

static inline bool gpu_resource_flush(int cli_id, gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (req->resource_flush.resource_id == GPU_DISABLE_SCANOUT_RESOURCE_ID
        || clients[cli_id].res_map_virt_to_drv[req->resource_flush.resource_id] == UNMAPPED_RESOURCE_ID) {
        LOG_GPU_VIRT_ERR("RESOURCE_FLUSH: Resource id invalid, failing request\n");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    if (drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_flush.resource_id]].is_blob) {
        if (!drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_flush.resource_id]].has_backing) {
            LOG_GPU_VIRT_ERR("RESOURCE_FLUSH: Blob resource has no backing, "
                             "failing request\n");
            fail_resp->status = GPU_RESP_ERR_UNSPEC;
            return false;
        }

        for (int i = 0; i < GPU_MAX_SCANOUTS; i++) {
            if (blob_scanouts[i][clients[cli_id].res_map_virt_to_drv[req->resource_flush.resource_id]].active
                && !rect_overlaps(
                    blob_scanouts[i][clients[cli_id].res_map_virt_to_drv[req->resource_flush.resource_id]].width,
                    blob_scanouts[i][clients[cli_id].res_map_virt_to_drv[req->resource_flush.resource_id]].height,
                    req->resource_flush.rect)) {
                LOG_GPU_VIRT_ERR("RESOURCE_FLUSH: Rectangle out of bounds from "
                                 "blob resource, failing request\n");
                fail_resp->status = GPU_RESP_ERR_INVALID_BOUNDS;
                return false;
            }
        }
    } else {
        if (!rect_overlaps(drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_flush.resource_id]].width,
                           drv_resources[clients[cli_id].res_map_virt_to_drv[req->resource_flush.resource_id]].height,
                           req->resource_flush.rect)) {
            LOG_GPU_VIRT_ERR("RESOURCE_FLUSH: Rectangle out of bounds from "
                             "resource, failing request\n");
            fail_resp->status = GPU_RESP_ERR_INVALID_BOUNDS;
            return false;
        }
    }

    reqsbk[drv_req->id].res_virt = req->resource_flush.resource_id;

    drv_req->code = GPU_REQ_RESOURCE_FLUSH;
    drv_req->resource_flush.resource_id = clients[cli_id].res_map_virt_to_drv[req->resource_flush.resource_id];
    drv_req->resource_flush.rect.x = req->resource_flush.rect.x;
    drv_req->resource_flush.rect.y = req->resource_flush.rect.y;
    drv_req->resource_flush.rect.width = req->resource_flush.rect.width;
    drv_req->resource_flush.rect.height = req->resource_flush.rect.height;
    return true;
}

static bool handle_client(int cli_id)
{
    int err = 0;
    bool driver_notify = false;
    bool client_notify = false;
    gpu_queue_handle_t *h = &clients[cli_id].queue_h;
    gpu_req_t req = { 0 };
    while (!gpu_queue_empty_req(h)) {
        err = gpu_dequeue_req(h, &req);
        assert(!err);

        LOG_GPU_VIRT("Received request %d from client %d\n", req.id, cli_id);

        if (req.code == GPU_REQ_GET_DISPLAY_INFO) {
            if (gpu_queue_full_resp(h)) {
                LOG_GPU_VIRT_ERR("Client %d request %d response queue is full, "
                                 "dropping get_display_info response\n",
                                 cli_id, req.id);
                continue;
            }
            client_notify = true;
            if (req.get_display_info.mem_offset + sizeof(gpu_resp_get_display_info_t)
                > gpu_virt_cli_data_region_size(cli_id)) {
                LOG_GPU_VIRT_ERR("GET_DISPLAY_INFO: Range in memory region to store display "
                                 "info is out of its allocated bounds, failing request\n");
                err = gpu_enqueue_resp(h, (gpu_resp_t) {
                    .id = req.id,
                    .status = GPU_RESP_ERR_INVALID_PARAMETER,
                });
                assert(!err);
                continue;
            }
            sddf_memcpy((void *)(gpu_virt_cli_data_region(gpu_client_data, cli_id) + req.get_display_info.mem_offset),
                        &get_display_info, sizeof(gpu_resp_get_display_info_t));
            err = gpu_enqueue_resp(h, (gpu_resp_t) {
                .id = req.id,
                .status = GPU_RESP_OK,
            });
            assert(!err);
            continue;
        }

        gpu_resp_t fail_resp = {
            .id = req.id,
            .status = GPU_RESP_ERR_UNSPEC,
        };

        if (ialloc_full(&req_ialloc)) {
            LOG_GPU_VIRT("Out of free request ids to allocate\n");
            break;
        }

        if (gpu_queue_full_req(&drv_h)) {
            LOG_GPU_VIRT("Driver request queue full\n");
            break;
        }

        gpu_req_t drv_req = { 0 };
        uint32_t drv_req_id = 0;
        int err = ialloc_alloc(&req_ialloc, &drv_req_id);
        assert(!err);
        drv_req.id = drv_req_id;

        reqsbk[drv_req_id].cli_id = cli_id;
        reqsbk[drv_req_id].cli_req_id = req.id;
        reqsbk[drv_req_id].code = req.code;

        bool success = false;
        switch (req.code) {
#ifdef GPU_BLOB_SUPPORT
        case GPU_REQ_RESOURCE_CREATE_BLOB: {
            success = gpu_resource_create_blob(cli_id, &req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_SET_SCANOUT_BLOB: {
            success = gpu_set_scanout_blob(cli_id, &req, &drv_req, &fail_resp);
            break;
        }
#endif
        case GPU_REQ_RESOURCE_CREATE_2D: {
            success = gpu_resource_create_2d(cli_id, &req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_RESOURCE_UNREF: {
            success = gpu_resource_unref(cli_id, &req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_RESOURCE_ATTACH_BACKING: {
            success = gpu_resource_attach_backing(cli_id, &req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_RESOURCE_DETACH_BACKING: {
            success = gpu_resource_detach_backing(cli_id, &req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_SET_SCANOUT: {
            success = gpu_set_scanout(cli_id, &req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_TRANSFER_TO_2D: {
            success = gpu_transfer_to_2d(cli_id, &req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_RESOURCE_FLUSH: {
            success = gpu_resource_flush(cli_id, &req, &drv_req, &fail_resp);
            break;
        }
        default: {
            LOG_GPU_VIRT_ERR("Unrecognised request code, failing request\n");
            fail_resp.status = GPU_RESP_ERR_UNSPEC;
            success = false;
            break;
        }
        }

        if (!success) {
            err = ialloc_free(&req_ialloc, drv_req_id);
            assert(!err);
            if (gpu_queue_full_resp(&clients[cli_id].queue_h)) {
                LOG_GPU_VIRT_ERR("Client %d request %d has failed AND response "
                                 "queue is also full, dropping response\n",
                                 cli_id, req.id);
                continue;
            }
            err = gpu_enqueue_resp(&clients[cli_id].queue_h, fail_resp);
            assert(!err);
            client_notify = true;
            continue;
        }

        err = gpu_enqueue_req(&drv_h, drv_req);
        assert(!err);
        driver_notify = true;
    }

    if (client_notify) {
        microkit_notify(clients[cli_id].ch);
    }

    return driver_notify;
}

static void handle_clients()
{
    bool notify = false;
    for (int i = 0; i < GPU_NUM_CLIENTS; i++) {
        if (handle_client(i)) {
            notify = true;
        }
    }
    if (notify) {
        microkit_notify(DRIVER_CH);
    }
}

static inline bool request_display_info()
{
    int err = 0;
    if (ialloc_full(&req_ialloc)) {
        LOG_GPU_VIRT_ERR("DISPLAY_INFO_EVENT: Out of free request ids to allocate\n");
        return false;
    }
    if (gpu_queue_full_req(&drv_h)) {
        LOG_GPU_VIRT_ERR("DISPLAY_INFO_EVENT: Driver request queue full\n");
        return false;
    }

    uint32_t drv_req_id = 0;
    err = ialloc_alloc(&req_ialloc, &drv_req_id);
    assert(!err);
    reqsbk[drv_req_id].cli_id = VIRTUALISER_ID;
    reqsbk[drv_req_id].cli_req_id = drv_req_id;
    reqsbk[drv_req_id].code = GPU_REQ_GET_DISPLAY_INFO;

    gpu_req_t drv_req = { 0 };
    drv_req.id = drv_req_id;
    drv_req.code = GPU_REQ_GET_DISPLAY_INFO;
    drv_req.get_display_info.mem_offset = 0;

    err = gpu_enqueue_req(&drv_h, drv_req);
    assert(!err);
    return true;
}

static void handle_driver()
{
    int err = 0;
    bool client_notify[GPU_NUM_CLIENTS] = { 0 };
    bool driver_notify = false;
    gpu_resp_t resp = { 0 };
    while (!gpu_queue_empty_resp(&drv_h)) {
        err = gpu_dequeue_resp(&drv_h, &resp);
        assert(!err);

        if (!ialloc_in_use(&req_ialloc, resp.id)) {
            LOG_GPU_VIRT_ERR("Driver response id invalid, dropping response\n");
            continue;
        }

        reqbk_t *reqbk = &reqsbk[resp.id];

        LOG_GPU_VIRT("Received response %d for client %d\n", reqbk->cli_req_id, reqbk->cli_id);

        if (reqbk->code == GPU_REQ_GET_DISPLAY_INFO) {
            err = ialloc_free(&req_ialloc, resp.id);
            assert(!err);
            if (resp.status == GPU_RESP_OK) {
                cache_clean_and_invalidate(gpu_driver_data, gpu_driver_data + sizeof(gpu_resp_get_display_info_t));
                sddf_memcpy(&get_display_info, (void *)gpu_driver_data, sizeof(gpu_resp_get_display_info_t));
                pending_display_info_request = false;
                try_again_display_info_req = false;
                /* Forward display info event to clients*/
                LOG_GPU_VIRT("Received display info data from driver, "
                             "forwarding display info event to clients\n");
                for (int i = 0; i < GPU_NUM_CLIENTS; i++) {
                    gpu_events_set_display_info(clients[i].events);
                    client_notify[i] = true;
                }
            } else {
                /* If display info request failed, keep trying */
                LOG_GPU_VIRT("Display info request failed\n");
                try_again_display_info_req = true;
            }
            continue;
        }

        gpu_resp_t cli_resp = {
            .id = reqbk->cli_req_id,
            .status = resp.status,
        };

        switch (reqbk->code) {
#ifdef GPU_BLOB_SUPPORT
        case GPU_REQ_RESOURCE_CREATE_BLOB: {
            if (resp.status != GPU_RESP_OK) {
                LOG_GPU_VIRT("Resource create blob response failed\n");
                err = ialloc_free(&res_ialloc, clients[reqbk->cli_id].res_map_virt_to_drv[reqbk->res_virt]);
                assert(!err);
                clients[reqbk->cli_id].res_map_virt_to_drv[reqbk->res_virt] = UNMAPPED_RESOURCE_ID;

                /* Clear any previously set scanout state */
                for (int i = 0; i < GPU_MAX_SCANOUTS; i++) {
                    blob_scanouts[i][reqbk->res_virt].active = false;
                }
            }
            break;
        }
#endif
        case GPU_REQ_RESOURCE_CREATE_2D: {
            if (resp.status != GPU_RESP_OK) {
                LOG_GPU_VIRT("Resource create 2d response failed\n");
                err = ialloc_free(&res_ialloc, clients[reqbk->cli_id].res_map_virt_to_drv[reqbk->res_virt]);
                assert(!err);
                clients[reqbk->cli_id].res_map_virt_to_drv[reqbk->res_virt] = UNMAPPED_RESOURCE_ID;
            }
            break;
        }
        case GPU_REQ_RESOURCE_UNREF:
            if (resp.status != GPU_RESP_OK) {
                LOG_GPU_VIRT("Resource unref response failed\n");
            }
            break;
        case GPU_REQ_RESOURCE_ATTACH_BACKING:
            if (resp.status != GPU_RESP_OK) {
                LOG_GPU_VIRT("Attach backing response failed\n");
            }
            break;
        case GPU_REQ_RESOURCE_DETACH_BACKING:
            if (resp.status != GPU_RESP_OK) {
                LOG_GPU_VIRT("Detach backing response failed\n");
            }
            break;
#ifdef GPU_BLOB_SUPPORT
        case GPU_REQ_SET_SCANOUT_BLOB:
            if (resp.status != GPU_RESP_OK) {
                LOG_GPU_VIRT("Set scanout blob response failed\n");
            }
            break;
#endif
        case GPU_REQ_SET_SCANOUT:
            if (resp.status != GPU_RESP_OK) {
                LOG_GPU_VIRT("Set scanout response failed\n");
            }
            break;
        case GPU_REQ_TRANSFER_TO_2D:
            if (resp.status != GPU_RESP_OK) {
                LOG_GPU_VIRT("Transfer to 2D response failed\n");
            }
            break;
        case GPU_REQ_RESOURCE_FLUSH:
            if (resp.status != GPU_RESP_OK) {
                LOG_GPU_VIRT("Resource flush response failed\n");
            }
            break;
        default: {
            /* This should never happen as we will have sanitised before bookkeeping an unrecognised req code */
            LOG_GPU_VIRT_ERR("Unrecognised bookkept request code, failing response\n");
            assert(false);
            break;
        }
        }

        err = ialloc_free(&req_ialloc, resp.id);
        assert(!err);

        if (gpu_queue_full_resp(&clients[reqbk->cli_id].queue_h)) {
            LOG_GPU_VIRT_ERR("Client %d response queue is full, dropping response id %d\n", reqbk->cli_id,
                             reqbk->cli_req_id);
            continue;
        }

        err = gpu_enqueue_resp(&clients[reqbk->cli_id].queue_h, cli_resp);
        assert(!err);
        client_notify[reqbk->cli_id] = true;
    }

    /* Handle display info event. There can only be one in-flight get display info request, and
     * if either the request cannot be enqueued due to high load, or the request has failed,
     * we will keep trying until it succeeds.
     */
    if (try_again_display_info_req) {
        LOG_GPU_VIRT("Retrying display info request\n");
        if (request_display_info()) {
            try_again_display_info_req = false;
            driver_notify = true;
        }
    }

    if (gpu_events_check_display_info(gpu_driver_events) && !pending_display_info_request) {
        LOG_GPU_VIRT("Received display info event from driver, sending display "
                     "info request\n");
        if (request_display_info()) {
            pending_display_info_request = true;
            gpu_events_clear_display_info(gpu_driver_events);
            driver_notify = true;
        } else {
            LOG_GPU_VIRT("Failed to send display info request\n");
            try_again_display_info_req = true;
        }
    }

    if (driver_notify) {
        microkit_notify(DRIVER_CH);
    }

    for (int i = 0; i < GPU_NUM_CLIENTS; i++) {
        if (client_notify[i]) {
            microkit_notify(clients[i].ch);
        }
    }
}
