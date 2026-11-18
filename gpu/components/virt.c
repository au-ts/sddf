/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/gpu/queue.h>
#include <sddf/gpu/events.h>
#include <sddf/gpu/config.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>
#include <sddf/util/cache.h>

/* Uncomment this to enable debug logging */
// #define DEBUG_GPU_VIRT

#if defined(DEBUG_GPU_VIRT)
#define LOG_GPU_VIRT(...) do{ sddf_dprintf("GPU_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_GPU_VIRT(...) do{}while(0)
#endif
#define LOG_GPU_VIRT_ERR(...) do{ sddf_dprintf("GPU_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

#define UNMAPPED_RESOURCE_ID UINT32_MAX
_Static_assert(
    GPU_MAX_RESOURCES <= UINT32_MAX - 2,
    "Resource ids can only occupy 32 bits of memory, with the smallest value of 0 reserved for disabling scanout and\
the largest value reserved for unmapped resources");

#define VIRTUALISER_ID UINT32_MAX
_Static_assert(SDDF_GPU_MAX_CLIENTS <= UINT32_MAX - 1, "Client ids can only occupy 32 bits of memory, with the "
                                                       "largest value reserved for virtualiser id itself");

__attribute__((__section__(".gpu_virt_config"))) gpu_virt_config_t config;

static gpu_events_t *gpu_driver_events;
static uintptr_t gpu_driver_data;

gpu_queue_handle_t drv_h;

typedef struct client {
    gpu_queue_handle_t queue_h;
    gpu_events_t *events;
    sddf_channel ch;
    /* Client's data region as mapped into the virtualiser */
    uintptr_t data_vaddr;
    uint64_t data_size;
    /* I/O address of the client's data region, as seen by the device */
    uint64_t data_io_addr;
    /* Mapping from virtualiser resource id to driver resource id */
    uint32_t res_map_virt_to_drv[GPU_MAX_RESOURCES + 1];
} client_t;
static client_t clients[SDDF_GPU_MAX_CLIENTS];
static uint32_t num_clients;
/* Driver resource id allocations */
static ialloc_t res_ialloc;
/* One larger than GPU_MAX_RESOURCES, id 0 is reserved at init for disabling scanout */
static uint32_t res_ialloc_idxlist[GPU_MAX_RESOURCES + 1];

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
/* Indexed by scanout id and driver resource id */
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
static reqbk_t reqsbk[SDDF_GPU_MAX_QUEUE_CAPACITY];
/* Virt-to-drv request id allocations */
static ialloc_t req_ialloc;
static uint32_t req_ialloc_idxlist[SDDF_GPU_MAX_QUEUE_CAPACITY];

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
    assert(gpu_config_check_magic(&config));
    assert(config.num_clients <= SDDF_GPU_MAX_CLIENTS);
    assert(config.driver.conn.num_buffers <= SDDF_GPU_MAX_QUEUE_CAPACITY);

    num_clients = config.num_clients;
    gpu_driver_events = (gpu_events_t *)config.driver.conn.events.vaddr;
    gpu_driver_data = (uintptr_t)config.driver.data.region.vaddr;
    assert(config.driver.data.region.size >= sizeof(gpu_resp_get_display_info_t));

    ialloc_init(&req_ialloc, req_ialloc_idxlist, config.driver.conn.num_buffers);
    ialloc_init(&res_ialloc, res_ialloc_idxlist, GPU_MAX_RESOURCES + 1);
    /* Reserve GPU_DISABLE_SCANOUT_RESOURCE_ID so that it is never handed to a resource */
    uint32_t reserved_res_id;
    int err = ialloc_alloc(&res_ialloc, &reserved_res_id);
    assert(!err && reserved_res_id == GPU_DISABLE_SCANOUT_RESOURCE_ID);

    /* Initialise client queues */
    for (int i = 0; i < num_clients; i++) {
        gpu_virt_config_client_t *cli_config = &config.clients[i];
        assert(cli_config->conn.num_buffers <= SDDF_GPU_MAX_QUEUE_CAPACITY);
        gpu_queue_init_from_conn(&clients[i].queue_h, &cli_config->conn);
        clients[i].events = (gpu_events_t *)cli_config->conn.events.vaddr;
        clients[i].ch = cli_config->conn.id;
        clients[i].data_vaddr = (uintptr_t)cli_config->data.region.vaddr;
        clients[i].data_size = cli_config->data.region.size;
        clients[i].data_io_addr = cli_config->data.io_addr;
        for (int j = 1; j < GPU_MAX_RESOURCES + 1; j++) {
            clients[i].res_map_virt_to_drv[j] = UNMAPPED_RESOURCE_ID;
        }
    }

    gpu_queue_init_from_conn(&drv_h, &config.driver.conn);
    LOG_GPU_VIRT("Requesting initial display info\n");
    init_request_get_display_info();
}

void notified(sddf_channel ch)
{
#ifdef DEBUG_GPU_VIRT
    if (ch == config.driver.conn.id) {
        LOG_GPU_VIRT("Received notification from driver\n");
    } else {
        LOG_GPU_VIRT("Received notification on channel %d\n", ch);
    }
#endif
    if (!display_info_init) {
        if (ch == config.driver.conn.id && handle_init_get_display_info_response()) {
            display_info_init = true;
            LOG_GPU_VIRT("Initialised display info\n");
        } else {
            return;
        }
    }

    if (ch == config.driver.conn.id) {
        handle_driver();
        /* We need to handle the client queues aswell, due to the scenario that we haven't fully
         * handled them when either the driver request queue or bookkeeping structures are full. When
         * the virtualiser has been notified by the driver, we know these structures can be
         * freed for the virtualiser to then forward more client requests. */
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
    sddf_notify(config.driver.conn.id);
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
    memcpy(&get_display_info, (void *)gpu_driver_data, sizeof(gpu_resp_get_display_info_t));
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

    if (req->resource_create_blob.mem_offset + req->resource_create_blob.mem_size > clients[cli_id].data_size) {
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
    /* The driver hands this address straight to the device */
    drv_req->resource_create_blob.mem_offset = clients[cli_id].data_io_addr + req->resource_create_blob.mem_offset;
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

    uint32_t drv_res_id = clients[cli_id].res_map_virt_to_drv[req->set_scanout_blob.resource_id];
    blob_scanouts[req->set_scanout_blob.scanout_id][drv_res_id].active = true;
    blob_scanouts[req->set_scanout_blob.scanout_id][drv_res_id].width = req->set_scanout_blob.width;
    blob_scanouts[req->set_scanout_blob.scanout_id][drv_res_id].height = req->set_scanout_blob.height;

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
    /* Not used for 2D resources */
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

    if (req->resource_attach_backing.mem_offset + req->resource_attach_backing.mem_size > clients[cli_id].data_size) {
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
    /* The driver hands this address straight to the device */
    drv_req->resource_attach_backing.mem_offset = clients[cli_id].data_io_addr
                                                + req->resource_attach_backing.mem_offset;
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
        (unsigned long)(clients[cli_id].data_vaddr
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
    while (!gpu_queue_empty_req(h) && !ialloc_full(&req_ialloc) && !gpu_queue_full_req(&drv_h)) {
        err = gpu_dequeue_req(h, &req);
        assert(!err);

        LOG_GPU_VIRT("Received request %d from client %d\n", req.id, cli_id);

        /* The virtualiser can respond directly to a GET_DISPLAY_INFO request from a client
         * without notifying the driver. We handle this separately here.
         */
        if (req.code == GPU_REQ_GET_DISPLAY_INFO) {
            client_notify = true;
            if (req.get_display_info.mem_offset + sizeof(gpu_resp_get_display_info_t) > clients[cli_id].data_size) {
                LOG_GPU_VIRT_ERR("GET_DISPLAY_INFO: Range in memory region to store display "
                                 "info is out of its allocated bounds, failing request\n");
                err = gpu_enqueue_resp(h, (gpu_resp_t) {
                                              .id = req.id,
                                              .status = GPU_RESP_ERR_INVALID_PARAMETER,
                                          });
                assert(!err);
                continue;
            }
            memcpy((void *)(clients[cli_id].data_vaddr + req.get_display_info.mem_offset), &get_display_info,
                   sizeof(gpu_resp_get_display_info_t));
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
        sddf_notify(clients[cli_id].ch);
    }

    return driver_notify;
}

static void handle_clients()
{
    bool notify = false;
    for (int i = 0; i < num_clients; i++) {
        if (handle_client(i)) {
            notify = true;
        }
    }
    if (notify) {
        sddf_notify(config.driver.conn.id);
    }
}

static inline bool request_display_info()
{
    int err = 0;
    if (ialloc_full(&req_ialloc) || gpu_queue_full_req(&drv_h)) {
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
    bool client_notify[SDDF_GPU_MAX_CLIENTS] = { 0 };
    bool driver_notify = false;
    gpu_resp_t resp = { 0 };

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
            LOG_GPU_VIRT("High load, failed to send display info request\n");
            try_again_display_info_req = true;
        }
    }

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
                memcpy(&get_display_info, (void *)gpu_driver_data, sizeof(gpu_resp_get_display_info_t));
                pending_display_info_request = false;
                try_again_display_info_req = false;
                /* Forward display info event to clients*/
                LOG_GPU_VIRT("Received display info data from driver, "
                             "forwarding display info event to clients\n");
                for (int i = 0; i < num_clients; i++) {
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
                uint32_t drv_res_id = clients[reqbk->cli_id].res_map_virt_to_drv[reqbk->res_virt];
                err = ialloc_free(&res_ialloc, drv_res_id);
                assert(!err);
                clients[reqbk->cli_id].res_map_virt_to_drv[reqbk->res_virt] = UNMAPPED_RESOURCE_ID;

                /* Clear any previously set scanout state */
                for (int i = 0; i < GPU_MAX_SCANOUTS; i++) {
                    blob_scanouts[i][drv_res_id].active = false;
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

        err = gpu_enqueue_resp(&clients[reqbk->cli_id].queue_h, cli_resp);
        assert(!err);
        client_notify[reqbk->cli_id] = true;
    }

    if (driver_notify) {
        sddf_notify(config.driver.conn.id);
    }

    for (int i = 0; i < num_clients; i++) {
        if (client_notify[i]) {
            sddf_notify(clients[i].ch);
        }
    }
}
