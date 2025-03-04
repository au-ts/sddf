/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/util/string.h>

#define BLK_NUM_CLIENTS                         1

#define BLK_NAME_CLI0                           "client"

#define BLK_QUEUE_CAPACITY_CLI0                 1024
#define BLK_QUEUE_CAPACITY_DRIV                 BLK_QUEUE_CAPACITY_CLI0

#define BLK_QUEUE_REGION_SIZE                   0xa00000
#define BLK_DATA_REGION_SIZE_CLI0               BLK_QUEUE_REGION_SIZE
#define BLK_DATA_REGION_SIZE_DRIV               BLK_QUEUE_REGION_SIZE

/* Mapping from client index to disk partition that the client will have access to. */
#if defined(MICROKIT_BOARD_odroidc4)
static const int blk_partition_mapping[BLK_NUM_CLIENTS] = { 0 };
#elif defined(MICROKIT_BOARD_qemu_virt_aarch64)
static const int blk_partition_mapping[BLK_NUM_CLIENTS] = { 0 };
#elif defined(MICROKIT_BOARD_maaxboard)
static const int blk_partition_mapping[BLK_NUM_CLIENTS] = { 2 };
#else
// XXX: should be defined for all boards, only these boards are supported, what to do?
#endif
static inline blk_storage_info_t *blk_virt_cli_storage_info(blk_storage_info_t *info, unsigned int id)
{
    switch (id) {
    case 0:
        return info;
    default:
        return NULL;
    }
}

static inline uintptr_t blk_virt_cli_data_region(uintptr_t data, unsigned int id)
{
    switch (id) {
    case 0:
        return data;
    default:
        return 0;
    }
}

static inline uint64_t blk_virt_cli_data_region_size(unsigned int id)
{
    switch (id) {
    case 0:
        return BLK_DATA_REGION_SIZE_CLI0;
    default:
        return 0;
    }
}

static inline blk_req_queue_t *blk_virt_cli_req_queue(blk_req_queue_t *req, unsigned int id)
{
    switch (id) {
    case 0:
        return req;
    default:
        return NULL;
    }
}

static inline blk_resp_queue_t *blk_virt_cli_resp_queue(blk_resp_queue_t *resp, unsigned int id)
{
    switch (id) {
    case 0:
        return resp;
    default:
        return NULL;
    }
}

static inline uint32_t blk_virt_cli_queue_capacity(unsigned int id)
{
    switch (id) {
    case 0:
        return BLK_QUEUE_CAPACITY_CLI0;
    default:
        return 0;
    }
}

static inline uint32_t blk_cli_queue_capacity(char *pd_name)
{
    if (!sddf_strcmp(pd_name, BLK_NAME_CLI0)) {
        return BLK_QUEUE_CAPACITY_CLI0;
    } else {
        return 0;
    }
}
