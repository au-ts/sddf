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
    uint32_t gen;
    // TODO: This resource id can be ANY NUMBER (uint32_t)!, this will not work!
    ialloc_t res_ialloc; /* index allocator for virtualiser-driver resource ids mapping */
    uint32_t res_ialloc_idxlist[GPU_MAX_RESOURCES];
    ialloc_t so_ialloc; /* index allocator for virtualiser-driver scanout ids mapping */
    uint32_t so_ialloc_idxlist[GPU_MAX_SCANOUTS];
} client_t;
static client_t clients[GPU_NUM_CLIENTS];

/* Bookkeeping struct per request */
typedef struct reqbk {
    uint32_t cli_id;
    uint32_t cli_req_id;
    uint32_t cli_req_gen;
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

void init(void)
{
    ialloc_init(&req_ialloc, req_ialloc_idxlist, REQBK_SIZE);
    fsmalloc_init(&fsmalloc, gpu_data_driver, GPU_DATA_CELL_SIZE, GPU_DATA_NUM_CELLS_DRIV,
                &fsmalloc_avail_bitarr, fsmalloc_avail_bitarr_words, roundup_bits2words64(GPU_DATA_NUM_CELLS_DRIV));
    // Initialise client queues
    for (int i = 0; i < GPU_NUM_CLIENTS; i++) {
        gpu_req_queue_t *curr_req = gpu_virt_cli_req_queue(gpu_req_queue_cli, i);
        gpu_resp_queue_t *curr_resp = gpu_virt_cli_resp_queue(gpu_resp_queue_cli, i);
        gpu_config_queue_t *curr_config = gpu_virt_cli_config_queue(gpu_config_queue_cli, i);
        uint32_t queue_capacity = gpu_virt_cli_queue_capacity(i);
        uint32_t config_queue_capacity = gpu_virt_cli_config_queue_capacity(i);
        gpu_queue_init(&clients[i].queue_h, curr_req, curr_resp, curr_config, queue_capacity, config_queue_capacity);

        ialloc_init(&clients[i].res_ialloc, &clients[i].res_ialloc_idxlist, GPU_MAX_RESOURCES);
        ialloc_init(&clients[i].so_ialloc, &clients[i].so_ialloc_idxlist, GPU_MAX_SCANOUTS);
        clients[i].ch = CLI_CH_OFFSET + i;
    }

    gpu_queue_init(&drv_h, gpu_req_queue_driver, gpu_resp_queue_driver, gpu_config_queue_driver,
                    GPU_QUEUE_CAPACITY_DRIV, GPU_CONFIG_QUEUE_CAPACITY_DRIV);
}

static bool map_request() {

}

static bool map_resource() {

}

static bool map_scanout() {

}

static void handle_driver()
{
    gpu_response_t resp;
    while (!gpu_resp_queue_empty(&drv_h)) {
        gpu_dequeue_resp(&drv_h, &resp);

        // use reqbk to get client req id, then send response to client
    }
}

static void handle_client(int cli_id)
{
    gpu_queue_handle_t *h = clients[cli_id].queue_h;

    gpu_request_t req;
    while (!gpu_req_queue_empty(h)) {
        gpu_dequeue_req(h, &req);

        gpu_response_t fail_resp = {
            .id = req.id,
            .status = GPU_RESP_ERR_UNSPEC,
        };

        if (ialloc_full(&req_ialloc) || gpu_req_queue_full(&drv_h)) {
            if (ialloc_full(&req_ialloc)) {
                LOG_GPU_VIRT_ERR("Driver request bookkeeping full, failing request\n");
            }
            if (gpu_req_queue_full(&drv_h)) {
                LOG_GPU_VIRT_ERR("Driver request queue full, failing request\n");
            }
            goto req_fail;
        }

        if (clients[cli_id].gen != req.gen) {
            LOG_GPU_VIRT("Configuration changed, failing request\n");
            fail_resp.status = GPU_RESP_ERR_CONFIG_CHANGE;
            goto req_fail;
        }

        uint32_t drv_req_id = 0;
        ialloc_alloc(&req_ialloc, &drv_req_id);

        switch (req.code) {
        case GPU_CMD_RESOURCE_CREATE_2D: {
            if (ialloc_full(&clients[cli_id].res_ialloc)) {
                LOG_GPU_VIRT("Resource mapping full, failing request");
                goto req_fail;
            }

            uint32_t drv_res_id = 0;
            ialloc_alloc(&clients[cli_id].res_ialloc, &drv_res_id);
            gpu_request_t drv_req = {
                .code = GPU_CMD_RESOURCE_CREATE_2D,
                .gen = drv_config.gen,
                .id = drv_req_id,
                .resource_create_2d.resource_id = drv_res_id,
                .resource_create_2d.width = req.resource_create_2d.width,
                .resource_create_2d.height = req.resource_create_2d.height,
                .resource_create_2d.format = req.resource_create_2d.format,
            };
            gpu_enqueue_req(&drv_h, &req);
            break;
        }
        case GPU_CMD_RESOURCE_UNREF: {
            gpu_request_t drv_req = {
                .code = GPU_CMD_RESOURCE_UNREF,
                .gen = drv_config.gen,
                .id = drv_req_id,
                // TODO: need mapping from virtualiser resource id to driver resource id...
                .resource_unref.resource_id = 0;
            }
            break;
        }
        case GPU_CMD_RESOURCE_ATTACH_BACKING: {

            break;
        }
        case GPU_CMD_RESOURCE_DETACH_BACKING: {
            break;
        }
        case GPU_CMD_SET_SCANOUT: {
            break;
        }
        case GPU_CMD_TRANSFER_TO_2D: {
            break;
        }
        case GPU_CMD_RESOURCE_FLUSH: {
            break;
        }
        default: {
            LOG_GPU_VIRT_ERR("Unrecognised request code, failing request");
            goto req_fail;
        }
        }

        reqbk[drv_req_id].cli_id = cli_id;
        reqbk[drv_req_id].cli_req_id = req.id;
        reqbk[drv_req_id].cli_req_gen = req.gen;

        continue;
req_fail:
        if (!gpu_resp_queue_full(&clients[cli_id].queue_h)) {
            gpu_enqueue_resp(&clients[cli_id].queue_h, &fail_resp);
        } else {
            LOG_GPU_VIRT_ERR("Request has failed AND response queue is also full, dropping request");
        }
    }
}

void notified(microkit_channel ch)
{
    if (!initialised) {
        if (!gpu_config_queue_empty(&drv_h)) {
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
