/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/cache.h>
#include <sddf/util/printf.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>

#include "virt.h"

#define DRIVER_MAX_NUM_BUFFERS 1024

__attribute__((__section__(".blk_virt_config"))) blk_virt_config_t config;

/* Driver queue handle */
blk_queue_handle_t drv_h;
/* Client queue handles */
blk_queue_handle_t client_queues[SDDF_BLK_MAX_CLIENTS];

/* Request info to be bookkept from client */
typedef struct reqbk {
    uint32_t cli_id;
    uint32_t cli_req_id;
    uintptr_t vaddr;
    uint16_t count;
    blk_req_code_t code;
} reqbk_t;
static reqbk_t reqsbk[DRIVER_MAX_NUM_BUFFERS];

/* Index allocator for driver request id */
ialloc_t ialloc;
static uint32_t ialloc_idxlist[DRIVER_MAX_NUM_BUFFERS];

bool initialised = false;

void init(void)
{
    assert(blk_config_check_magic(&config));

    blk_storage_info_t *driver_storage_info = config.driver.conn.storage_info.vaddr;
    while (!blk_storage_is_ready(driver_storage_info));

    /* Initialise client queues */
    for (int i = 0; i < config.num_clients; i++) {
        blk_virt_config_client_t *client = &config.clients[i];
        blk_req_queue_t *curr_req = client->conn.req_queue.vaddr;
        blk_resp_queue_t *curr_resp = client->conn.resp_queue.vaddr;
        uint32_t queue_capacity = client->conn.num_buffers;
        blk_queue_init(&client_queues[i], curr_req, curr_resp, queue_capacity);
    }

    /* Initialise driver queue */
    uint16_t driver_num_buffers = config.driver.conn.num_buffers;
    assert(driver_num_buffers <= DRIVER_MAX_NUM_BUFFERS);
    blk_queue_init(&drv_h, config.driver.conn.req_queue.vaddr, config.driver.conn.resp_queue.vaddr, driver_num_buffers);

    /* Initialise index allocator */
    ialloc_init(&ialloc, ialloc_idxlist, DRIVER_MAX_NUM_BUFFERS);

    virt_partition_init();
}

static void handle_driver()
{
    bool client_notify[SDDF_BLK_MAX_CLIENTS];
    sddf_memset(client_notify, 0, SDDF_BLK_MAX_CLIENTS);

    blk_resp_status_t drv_status = 0;
    uint16_t drv_success_count = 0;
    uint32_t drv_resp_id = 0;

    int err = 0;
    while (!blk_queue_empty_resp(&drv_h)) {
        err = blk_dequeue_resp(&drv_h, &drv_status, &drv_success_count, &drv_resp_id);
        assert(!err);

        reqbk_t reqbk = reqsbk[drv_resp_id];
        err = ialloc_free(&ialloc, drv_resp_id);
        assert(!err);

        switch (reqbk.code) {
        case BLK_REQ_READ:
            if (drv_status == BLK_RESP_OK) {
                /* Invalidate cache */
                cache_clean_and_invalidate(reqbk.vaddr, reqbk.vaddr + (BLK_TRANSFER_SIZE * reqbk.count));
            }
            break;
        case BLK_REQ_WRITE:
        case BLK_REQ_FLUSH:
        case BLK_REQ_BARRIER:
            break;
        default:
            /* This should never happen as we will have sanitized request codes before they are bookkept */
            LOG_BLK_VIRT_ERR("bookkept client %d request code %d is invalid, this should never happen\n", reqbk.cli_id,
                             reqbk.code);
            assert(false);
        }

        blk_queue_handle_t *h = &client_queues[reqbk.cli_id];

        /* Response queue should never be full since number of inflight requests (ialloc size)
         * should always be less than or equal to resp queue capacity.
         */
        err = blk_enqueue_resp(h, drv_status, drv_success_count, reqbk.cli_req_id);
        assert(!err);
        client_notify[reqbk.cli_id] = true;
    }

    /* Notify corresponding client if a response was enqueued */
    for (int i = 0; i < config.num_clients; i++) {
        if (client_notify[i]) {
            microkit_notify(config.clients[i].conn.id);
        }
    }
}

static bool handle_client(int cli_id)
{
    int err = 0;
    blk_queue_handle_t h = client_queues[cli_id];
    uintptr_t cli_data_base_paddr = config.clients[cli_id].data.io_addr;
    uintptr_t cli_data_base_vaddr = (uintptr_t)config.clients[cli_id].data.region.vaddr;
    uint64_t cli_data_region_size = config.clients[cli_id].data.region.size;

    blk_req_code_t cli_code = 0;
    uintptr_t cli_offset = 0;
    uint64_t cli_block_number = 0;
    uint16_t cli_count = 0;
    uint32_t cli_req_id = 0;

    bool driver_notify = false;
    bool client_notify = false;
    /*
     * In addition to checking the client actually has a request, we check that the
     * we can enqueue the request into the driver as well as that our index state tracking
     * is not full. We check the index allocator as there can be more in-flight requests
     * than currently in the driver queue.
     */
    while (!blk_queue_empty_req(&h) && !blk_queue_full_req(&drv_h) && !ialloc_full(&ialloc)) {

        err = blk_dequeue_req(&h, &cli_code, &cli_offset, &cli_block_number, &cli_count, &cli_req_id);
        assert(!err);

        uint64_t drv_block_number = 0;

        blk_resp_status_t resp_status = BLK_RESP_ERR_UNSPEC;

        switch (cli_code) {
        case BLK_REQ_READ:
        case BLK_REQ_WRITE: {
            resp_status = get_drv_block_number(cli_block_number, cli_count, cli_id, &drv_block_number);
            if (resp_status != BLK_RESP_OK) {
                goto req_fail;
            }

            if ((cli_offset + BLK_TRANSFER_SIZE * cli_count) > cli_data_region_size) {
                /* Requested offset is out of bounds from client data region */
                LOG_BLK_VIRT_ERR("client %d request offset 0x%lx is invalid\n", cli_id, cli_offset);
                resp_status = BLK_RESP_ERR_INVALID_PARAM;
                goto req_fail;
            }

            if (cli_count == 0) {
                LOG_BLK_VIRT_ERR("client %d requested zero blocks\n", cli_id);
                resp_status = BLK_RESP_ERR_INVALID_PARAM;
                goto req_fail;
            }

            if ((cli_data_base_vaddr + cli_offset) % BLK_TRANSFER_SIZE != 0) {
                LOG_BLK_VIRT_ERR(
                    "client %d requested dma address is not aligned to page size (same as blk transfer size)\n",
                    cli_id);
                resp_status = BLK_RESP_ERR_INVALID_PARAM;
                goto req_fail;
            }
            break;
        }
        case BLK_REQ_FLUSH:
        case BLK_REQ_BARRIER:
            break;
        default:
            /* Invalid request code given */
            LOG_BLK_VIRT_ERR("client %d gave an invalid request code %d\n", cli_id, cli_code);
            resp_status = BLK_RESP_ERR_INVALID_PARAM;
            goto req_fail;
        }

        if (cli_code == BLK_REQ_WRITE) {
            cache_clean(cli_data_base_vaddr + cli_offset,
                        cli_data_base_vaddr + cli_offset + (BLK_TRANSFER_SIZE * cli_count));
        }

        /* Bookkeep client request and generate driver req id */
        uint32_t drv_req_id = 0;
        err = ialloc_alloc(&ialloc, &drv_req_id);
        assert(!err);
        reqsbk[drv_req_id] = (reqbk_t) { cli_id, cli_req_id, cli_data_base_vaddr + cli_offset, cli_count, cli_code };

        err = blk_enqueue_req(&drv_h, cli_code, cli_data_base_paddr + cli_offset, drv_block_number, cli_count,
                              drv_req_id);
        assert(!err);
        driver_notify = true;
        continue;

    req_fail:
        /* Response queue should never be full since number of inflight requests (ialloc size)
         * should always be less than or equal to resp queue capacity.
         */
        err = blk_enqueue_resp(&h, resp_status, 0, cli_req_id);
        assert(!err);
        client_notify = true;
    }

    if (client_notify) {
        microkit_notify(config.clients[cli_id].conn.id);
    }

    return driver_notify;
}

static void handle_clients()
{
    bool driver_notify = false;
    for (int i = 0; i < config.num_clients; i++) {
        if (handle_client(i)) {
            driver_notify = true;
        }
    }

    if (driver_notify) {
        microkit_notify(config.driver.conn.id);
    }
}

void notified(microkit_channel ch)
{
    if (!initialised) {
        /* Continue processing partitions until initialisation has finished. */
        LOG_BLK_VIRT("initialising partitions\n");
        initialised = virt_partition_init();
    }

    if (ch == config.driver.conn.id) {
        handle_driver();
        handle_clients();
    } else {
        handle_clients();
    }
}
