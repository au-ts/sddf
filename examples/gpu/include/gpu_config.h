#pragma once

#include <stddef.h>
#include <sddf/util/string.h>
#include <sddf/gpu/queue.h>

#define GPU_DATA_CELL_SIZE 4096

#define GPU_NUM_CLIENTS 1

#define GPU_NAME_CLI0                      "client0"

#define GPU_QUEUE_CAPACITY_CLI0                 1024
#define GPU_QUEUE_CAPACITY_DRIV                 (GPU_QUEUE_CAPACITY_CLI0)
#define GPU_CONFIG_QUEUE_CAPACITY_CLI0          32
#define GPU_CONFIG_QUEUE_CAPACITY_DRIV          (GPU_CONFIG_QUEUE_CAPACITY_CLI0)

#define GPU_REGION_SIZE                     0x200000
#define GPU_DATA_REGION_SIZE_CLI0           GPU_REGION_SIZE
#define GPU_DATA_REGION_SIZE_DRIV           GPU_REGION_SIZE
#define GPU_QUEUE_REGION_SIZE_CLI0          GPU_REGION_SIZE
#define GPU_QUEUE_REGION_SIZE_DRIV          GPU_REGION_SIZE
#define GPU_CONFIG_QUEUE_REGION_SIZE_CLI0   GPU_REGION_SIZE
#define GPU_CONFIG_QUEUE_REGION_SIZE_DRIV   GPU_REGION_SIZE

static inline uintptr_t gpu_virt_cli_data_region(uintptr_t data, unsigned int id)
{
    switch (id) {
    case 0:
        return data;
    default:
        return 0;
    }
}

static inline gpu_req_queue_t *gpu_virt_cli_req_queue(gpu_req_queue_t *req, unsigned int id)
{
    switch (id) {
    case 0:
        return req;
    default:
        return NULL;
    }
}

static inline gpu_resp_queue_t *gpu_virt_cli_resp_queue(gpu_resp_queue_t *resp, unsigned int id)
{
    switch (id) {
    case 0:
        return resp;
    default: 
        return NULL;
    }
}

static inline gpu_config_queue_t *gpu_virt_cli_config_queue(gpu_config_queue_t *config, unsigned int id)
{
    switch (id) {
    case 0:
        return config;
    default:
        return NULL;
    }
}

static inline uint64_t gpu_virt_cli_data_region_size(unsigned int id)
{
    switch (id) {
    case 0:
        return GPU_DATA_REGION_SIZE_CLI0;
    default:
        return 0;
    }
}

static inline uint32_t gpu_virt_cli_queue_capacity(unsigned int id)
{
    switch (id) {
    case 0:
        return GPU_QUEUE_CAPACITY_CLI0;
    default:
        return 0;
    }
}

static inline uint32_t gpu_virt_cli_config_queue_capacity(unsigned int id)
{
    switch (id) {
    case 0:
        return GPU_CONFIG_QUEUE_CAPACITY_CLI0;
    default:
        return 0;
    }
}

static inline uint32_t gpu_cli_queue_capacity(char *pd_name)
{
    if (!sddf_strcmp(pd_name, GPU_NAME_CLI0)) {
        return GPU_QUEUE_CAPACITY_CLI0;
    } else {
        return 0;
    }
}

static inline uint32_t gpu_cli_config_queue_capacity(char *pd_name)
{
    if (!sddf_strcmp(pd_name, GPU_NAME_CLI0)) {
        return GPU_CONFIG_QUEUE_CAPACITY_CLI0;
    } else {
        return 0;
    }
}
