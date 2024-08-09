#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/gpu/queue.h>
#include <sddf/util/cache.h>
#include <sddf/util/fsmalloc.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <gpu_config.h>

/* Uncomment this to enable debug logging */
// #define DEBUG_GPU_VIRT

#if defined(DEBUG_GPU_VIRT)
#define LOG_GPU_VIRT(...) do{ sddf_dprintf("GPU_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_GPU_VIRT(...) do{}while(0)
#endif
#define LOG_GPU_VIRT_ERR(...) do{ sddf_dprintf("GPU_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

#define DRIVER_CH 0
#define CLI_CH_OFFSET 1

#define REQBK_SIZE GPU_QUEUE_CAPACITY_DRIV

#define GPU_DATA_NUM_CELLS_DRIV (GPU_DATA_REGION_SIZE_DRIV / GPU_DATA_CELL_SIZE)

#define INVALID_RES_ID UINT32_MAX

/* Microkit patched variables */
gpu_req_queue_t *gpu_req_queue_driver;
gpu_resp_queue_t *gpu_resp_queue_driver;
gpu_config_queue_t *gpu_config_queue_driver;
uintptr_t gpu_data_driver;

gpu_req_queue_t *gpu_req_queue_cli;
gpu_resp_queue_t *gpu_resp_queue_cli;
gpu_config_queue_t *gpu_config_queue_cli;
uintptr_t gpu_data_cli;

/* Driver queue handle */
gpu_queue_handle_t drv_h;
gpu_config_t drv_config;

/* Client info and queue handle */
typedef struct client {
    gpu_queue_handle_t queue_h;
    microkit_channel ch;
} client_t;
static client_t clients[GPU_NUM_CLIENTS];

/* Resource id mapping */
static ialloc_t res_ialloc; /* index allocator for driver resource ids mapping */
static uint32_t res_ialloc_idxlist[GPU_MAX_RESOURCES];
static uint32_t res_map_virt_to_drv[GPU_MAX_RESOURCES]; /* mapping from virtualiser resource id to driver resource id */

/* Bookkeeping struct per request */
typedef struct reqbk {
    uint32_t cli_id;
    uint32_t cli_req_id;
    uint32_t res_virt;
    gpu_req_code_t code;
} reqbk_t;
static reqbk_t reqbk[REQBK_SIZE];

/* Index allocator for request bookkeeping with driver */
static ialloc_t req_ialloc;
static uint32_t req_ialloc_idxlist[REQBK_SIZE];

/* Fixed size memory allocator for shared data region with driver */
static fsmalloc_t fsmalloc;
static bitarray_t fsmalloc_avail_bitarr;
static word_t fsmalloc_avail_bitarr_words[roundup_bits2words64(GPU_DATA_NUM_CELLS_DRIV)];

/* True when config is read from driver */
static bool initialised = false;

static void handle_client(int cli_id);
static void handle_driver(void);

void init(void)
{
    ialloc_init(&req_ialloc, req_ialloc_idxlist, REQBK_SIZE);
    fsmalloc_init(&fsmalloc, gpu_data_driver, GPU_DATA_CELL_SIZE, GPU_DATA_NUM_CELLS_DRIV,
                &fsmalloc_avail_bitarr, fsmalloc_avail_bitarr_words, roundup_bits2words64(GPU_DATA_NUM_CELLS_DRIV));
    ialloc_init(&res_ialloc, &res_ialloc_idxlist, GPU_MAX_RESOURCES);
    ialloc_init(&so_ialloc, &so_ialloc_idxlist, GPU_MAX_SCANOUTS);

    // Initialise client queues
    for (int i = 0; i < GPU_NUM_CLIENTS; i++) {
        gpu_req_queue_t *curr_req = gpu_virt_cli_req_queue(gpu_req_queue_cli, i);
        gpu_resp_queue_t *curr_resp = gpu_virt_cli_resp_queue(gpu_resp_queue_cli, i);
        gpu_config_queue_t *curr_config = gpu_virt_cli_config_queue(gpu_config_queue_cli, i);
        uint32_t curr_queue_capacity = gpu_virt_cli_queue_capacity(i);
        uint32_t curr_config_queue_capacity = gpu_virt_cli_config_queue_capacity(i);
        gpu_queue_init(&clients[i].queue_h, curr_req, curr_resp, curr_config, curr_queue_capacity, curr_config_queue_capacity);
        clients[i].ch = CLI_CH_OFFSET + i;
    }

    gpu_queue_init(&drv_h, gpu_req_queue_driver, gpu_resp_queue_driver, gpu_config_queue_driver,
                    GPU_QUEUE_CAPACITY_DRIV, GPU_CONFIG_QUEUE_CAPACITY_DRIV);
}

void notified(microkit_channel ch)
{
    if (!initialised) {
        if (ch == DRIVER_CH && !gpu_queue_empty_config(&drv_h)) {
            gpu_dequeue_config(&drv_h, &drv_config);
            initialised = true;
        } else {
            return;
        }
    }

    if (ch == DRIVER_CH) {
        handle_driver();
    } else {
        for (int i = 0; i < GPU_NUM_CLIENTS; i++) {
            handle_client(i);
        }
        microkit_notify_delayed(DRIVER_CH);
    }
}

static inline bool res_virt_valid(uint32_t virt_res_id)
{
    return res_map_virt_to_drv[virt_res_id] != INVALID_RES_ID;
}

static inline void res_virt_map(uint32_t virt_res_id, uint32_t drv_res_id)
{
    res_map_virt_to_drv[virt_res_id] = drv_res_id;
}

static inline void res_virt_unmap(uint32_t virt_res_id)
{
    res_map_virt_to_drv[virt_res_id] = INVALID_RES_ID;
}

static inline uint32_t res_virt_to_drv(uint32_t virt_res_id)
{
    return res_map_virt_to_drv[virt_res_id];
}

static inline bool gpu_resource_create_2d(gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (ialloc_full(&res_ialloc)) {
        LOG_GPU_VIRT_ERR("Resource mapping is full, failing request\n");
        fail_resp->status = GPU_RESP_ERR_UNSPEC;
        return false;
    }

    uint32_t drv_res_id = 0;
    ialloc_alloc(&res_ialloc, &drv_res_id);
    res_virt_map(req->resource_id, drv_res_id);
    drv_req->code = GPU_REQ_RESOURCE_CREATE_2D;
    drv_req->resource_id = drv_res_id;
    drv_req->resource_create_2d.width = req->resource_create_2d.width;
    drv_req->resource_create_2d.height = req->resource_create_2d.height;
    drv_req->resource_create_2d.format = req->resource_create_2d.format;
    return true;
}

static inline bool gpu_resource_unref(gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *resp)
{
    if (!res_virt_valid(req->resource_id)) {
        LOG_GPU_VIRT("Resource id invalid, failing request");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    drv_req->code = GPU_REQ_RESOURCE_UNREF;
    drv_req->resource_id = res_virt_to_drv(req->resource_id);
    ialloc_free(&res_ialloc, res_virt_to_drv(req->resource_id));
    res_virt_unmap(req->resource_id);
    return true;
}

static inline bool gpu_resource_attach_backing(gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (!res_virt_valid(req->resource_id)) {
        LOG_GPU_VIRT("Resource id invalid, failing request");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    drv_req->code = GPU_REQ_RESOURCE_ATTACH_BACKING;
    drv_req->resource_id = res_virt_to_drv(req->resource_id);
    drv_req->resource_attach_backing.io_or_offset = req->resource_attach_backing.io_or_offset; // TODO: convert offset to I/O address
    drv_req->resource_attach_backing.data_size = req->resource_attach_backing.data_size;
    return true;
}

static inline bool gpu_resource_detach_backing(gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (!res_virt_valid(req->resource_id)) {
        LOG_GPU_VIRT("Resource id invalid, failing request");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    drv_req->code = GPU_REQ_RESOURCE_DETACH_BACKING;
    drv_req->resource_id = res_virt_to_drv(req->resource_id);
    return true;
}

static inline bool gpu_set_scanout(gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    // TODO: REVISIT
    // so_map_virt_to_drv[req.set_scanout.scanout_id] = drv_so_id;
    // so_map_drv_to_virt[drv_so_id] = req.set_scanout.scanout_id;
    drv_req.code = GPU_REQ_SET_SCANOUT;
    drv_req.id = drv_req_id;
    // drv_req.set_scanout.scanout_id = drv_so_id;
    drv_req.set_scanout.resource_id = res_virt_to_drv(req.resource_id);
    drv_req.set_scanout.rect.x = req.set_scanout.rect.x;
    drv_req.set_scanout.rect.y = req.set_scanout.rect.y;
    drv_req.set_scanout.rect.width = req.set_scanout.rect.width;
    drv_req.set_scanout.rect.height = req.set_scanout.rect.height;
    return false;
}

static inline bool gpu_transfer_to_2d(gpu_req_t *req, gpu_req_t *drv_req, gpu_resp_t *fail_resp)
{
    if (!res_virt_valid(req->resource_id)) {
        LOG_GPU_VIRT("Resource id invalid, failing request");
        fail_resp->status = GPU_RESP_ERR_INVALID_RESOURCE_ID;
        return false;
    }

    drv_req->code = GPU_REQ_TRANSFER_TO_2D;
    drv_req->resource_id = res_virt_to_drv(req->resource_id);
    drv_req->transfer_to_2d.rect.x = req->transfer_to_2d.rect.x;
    drv_req->transfer_to_2d.rect.y = req->transfer_to_2d.rect.y;
    drv_req->transfer_to_2d.rect.width = req->transfer_to_2d.rect.width;
    drv_req->transfer_to_2d.rect.height = req->transfer_to_2d.rect.height;
    drv_req->transfer_to_2d.offset = req->transfer_to_2d.offset;
    return true;
}

static void handle_client(int cli_id)
{
    gpu_queue_handle_t *h = clients[cli_id].queue_h;

    gpu_req_t req;
    while (!gpu_queue_empty_req(h)) {
        gpu_dequeue_req(h, &req);

        gpu_resp_t fail_resp = {
            .id = req.id,
            .status = GPU_RESP_ERR_UNSPEC,
        };

        if (ialloc_full(&req_ialloc)) {
            LOG_GPU_VIRT_ERR("Driver request bookkeeping full, failing request\n");
            goto req_fail;
        }
        
        if (gpu_queue_full_req(&drv_h)) {
            LOG_GPU_VIRT_ERR("Driver request queue full, failing request\n");
            goto req_fail;
        }

        gpu_req_t drv_req = 0;        
        bool success = false;
        switch (req.code) {
        case GPU_REQ_RESOURCE_CREATE_2D: {
            success = gpu_resource_create_2d(&req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_RESOURCE_UNREF: {
            success = gpu_resource_unref(&req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_RESOURCE_ATTACH_BACKING: {
            success = gpu_resource_attach_backing(&req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_RESOURCE_DETACH_BACKING: {
            success = gpu_resource_detach_backing(&req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_SET_SCANOUT: {
            success = gpu_set_scanout(&req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_TRANSFER_TO_2D: {
            success = gpu_transfer_to_2d(&req, &drv_req, &fail_resp);
            break;
        }
        case GPU_REQ_RESOURCE_FLUSH: {
            success = gpu_resource_flush(&req, &drv_req, &fail_resp);
            break;
        }
        default: {
            LOG_GPU_VIRT_ERR("Unrecognised request code, failing request");
            break;
        }
        }

        if (!success) {
            goto req_fail;
        }

        uint32_t drv_req_id = 0;
        ialloc_alloc(&req_ialloc, &drv_req_id);
        drv_req.id = drv_req_id;

        reqbk[drv_req_id].cli_id = cli_id;
        reqbk[drv_req_id].cli_req_id = req.id;
        reqbk[drv_req_id].code = req.code;
        reqbk[drv_req_id].res_virt = req.resource_id;

        gpu_enqueue_req(&drv_h, &drv_req);
        continue;
req_fail:
        if (!gpu_queue_full_resp(&clients[cli_id].queue_h)) {
            gpu_enqueue_resp(&clients[cli_id].queue_h, &fail_resp);
        } else {
            LOG_GPU_VIRT_ERR("Request has failed AND response queue is also full, dropping request");
        }
    }
}

static void handle_driver()
{
    gpu_resp_t resp;
    while (!gpu_queue_empty_resp(&drv_h)) {
        gpu_dequeue_resp(&drv_h, &resp);

        if (!ialloc_in_use(&req_ialloc, resp.id)) {
            LOG_GPU_VIRT_ERR("Driver response id invalid, dropping response\n");
            continue;
        }

        reqbk_t *bk = &reqbk[resp.id];
        gpu_resp_t cli_resp = {
            .id = bk->cli_req_id,
            .status = resp.status,
        };
        
        switch (bk->code) {
        case GPU_REQ_RESOURCE_CREATE_2D: {
            if (resp.status != GPU_RESP_OK) {
                ialloc_free(&res_ialloc, res_virt_to_drv(bk->res_virt));
                res_unmap(bk->res_virt);
            }
            break;
        }
        case GPU_REQ_RESOURCE_ATTACH_BACKING: {
            if (resp.status != GPU_RESP_OK) {
                // TODO: free allocations in data region
            }
            break;
        }
        case GPU_REQ_RESOURCE_DETACH_BACKING:
        case GPU_REQ_RESOURCE_UNREF:
        case GPU_REQ_SET_SCANOUT:
        case GPU_REQ_TRANSFER_TO_2D:
            break;
        default: {
            /* This will never happen as we will have sanitised before bookkeeping an unrecognised req code */
            LOG_GPU_VIRT_ERR("Unrecognised bookkept request code, something has gone really wrong...");
            break;
        }
        }

        ialloc_free(&req_ialloc, resp.id);
        gpu_enqueue_resp(&clients[bk->cli_id].queue_h, &cli_resp);
        notify(clients[bk->cli_id].ch);
    }
}
