/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/blk/queue.h>
#include <sddf/util/cache.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>

#include "virt.h"

/* Microkit patched variables */
blk_storage_info_t *blk_driver_storage_info;
blk_req_queue_t *blk_driver_req_queue;
blk_resp_queue_t *blk_driver_resp_queue;
uintptr_t blk_driver_data;
uintptr_t blk_data_paddr_driver;
blk_storage_info_t *blk_client_storage_info;
blk_req_queue_t *blk_client_req_queue;
blk_resp_queue_t *blk_client_resp_queue;
uintptr_t blk_client_data;
uintptr_t blk_client0_data_paddr;
uintptr_t blk_client1_data_paddr;

/* Driver queue handle */
blk_queue_handle_t drv_h;

/* Client specific info */
typedef struct client {
    blk_queue_handle_t queue_h;
    microkit_channel ch;
    uintptr_t data_paddr;
} client_t;
client_t clients[BLK_NUM_CLIENTS];

/* Request info to be bookkept from client */
typedef struct reqbk {
    uint32_t cli_id;
    uint32_t cli_req_id;
    uintptr_t vaddr;
    uint16_t count;
    blk_req_code_t code;
} reqbk_t;
static reqbk_t reqsbk[BLK_QUEUE_CAPACITY_DRIV];

/* Index allocator for driver request id */
ialloc_t ialloc;
static uint32_t ialloc_idxlist[BLK_QUEUE_CAPACITY_DRIV];

static enum {
    VirtInactive,
    VirtBringup,
    VirtReady,
} virt_status = VirtInactive;

static void handle_driver_state();

void init(void)
{
    while (!blk_storage_is_ready(blk_driver_storage_info));

    /* Initialise client queues */
    for (int i = 0; i < BLK_NUM_CLIENTS; i++) {
        blk_req_queue_t *curr_req = blk_virt_cli_req_queue(blk_client_req_queue, i);
        blk_resp_queue_t *curr_resp = blk_virt_cli_resp_queue(blk_client_resp_queue, i);
        uint32_t queue_capacity = blk_virt_cli_queue_capacity(i);
        blk_queue_init(&clients[i].queue_h, curr_req, curr_resp, queue_capacity);
        clients[i].ch = CLI_CH_OFFSET + i;
    }

    /* TODO: make data paddr handling system agnostic */
    assert(BLK_NUM_CLIENTS <= 2 && BLK_NUM_CLIENTS >= 1);
    clients[0].data_paddr = blk_client0_data_paddr;
    if (BLK_NUM_CLIENTS > 1) {
        clients[1].data_paddr = blk_client1_data_paddr;
    }

    /* Initialise driver queue */
    blk_queue_init(&drv_h, blk_driver_req_queue, blk_driver_resp_queue, BLK_QUEUE_CAPACITY_DRIV);

    /* Initialise index allocator */
    ialloc_init(&ialloc, ialloc_idxlist, BLK_QUEUE_CAPACITY_DRIV);

    handle_driver_state();
}

static void notify_clients_state()
{
    bool driver_ready = blk_storage_is_ready(blk_driver_storage_info);
    for (int i = 0; i < BLK_NUM_CLIENTS; i++) {
        blk_storage_info_t *cli_storage_info = blk_virt_cli_storage_info(blk_client_storage_info, i);

        __atomic_store_n(&cli_storage_info->ready, driver_ready, __ATOMIC_RELEASE);
    }
}

static void handle_driver_state()
{
    bool driver_ready = blk_storage_is_ready(blk_driver_storage_info);

    /* As per the documentation, if we receive a BLK_STATE_CH notification
       we must treat it as if the device went In -> Out -> In even if we only
       ever see the In state.
       This actually makes our lives easier, because of instead of 4 states we
       only have two ( {drv_ready, us_ready}  ->   {drv_ready} ).
    */

    if (driver_ready) {
        policy_reset();
        virt_status = VirtBringup;
        bool done = policy_init();
        if (done) {
            /* keep in sync with notified() */
            virt_status = VirtReady;
            notify_clients_state();
        }
    } else {
        virt_status = VirtInactive;
        policy_reset();
        notify_clients_state();
    }
}

static void handle_driver_queue()
{
    bool client_notify[BLK_NUM_CLIENTS] = { 0 };

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
                /* TODO: This is a raw seL4 system call because Microkit does not (currently)
                    * include a corresponding libmicrokit API. */
                seL4_ARM_VSpace_Invalidate_Data(3, reqbk.vaddr, reqbk.vaddr + (BLK_TRANSFER_SIZE * reqbk.count));
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

        blk_queue_handle_t h = clients[reqbk.cli_id].queue_h;

        /* Response queue should never be full since number of inflight requests (ialloc size)
         * should always be less than or equal to resp queue capacity.
         */
        err = blk_enqueue_resp(&h, drv_status, drv_success_count, reqbk.cli_req_id);
        assert(!err);
        client_notify[reqbk.cli_id] = true;
    }

    /* Notify corresponding client if a response was enqueued */
    for (int i = 0; i < BLK_NUM_CLIENTS; i++) {
        if (client_notify[i]) {
            microkit_notify(clients[i].ch);
        }
    }
}

static bool handle_client(int cli_id)
{
    int err = 0;
    blk_queue_handle_t h = clients[cli_id].queue_h;
    uintptr_t cli_data_base = blk_virt_cli_data_region(blk_client_data, cli_id);
    uint64_t cli_data_region_size = blk_virt_cli_data_region_size(cli_id);

    blk_req_code_t cli_code = 0;
    uintptr_t cli_offset = 0;
    uint32_t cli_block_number = 0;
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

        uint32_t drv_block_number = 0;

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

            if ((clients[cli_id].data_paddr + cli_offset) % BLK_TRANSFER_SIZE != 0) {
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
            cache_clean(cli_data_base + cli_offset, cli_data_base + cli_offset + (BLK_TRANSFER_SIZE * cli_count));
        }

        /* Bookkeep client request and generate driver req id */
        uint32_t drv_req_id = 0;
        err = ialloc_alloc(&ialloc, &drv_req_id);
        assert(!err);
        reqsbk[drv_req_id] = (reqbk_t) { cli_id, cli_req_id, cli_data_base + cli_offset, cli_count, cli_code };

        err = blk_enqueue_req(&drv_h, cli_code, clients[cli_id].data_paddr + cli_offset, drv_block_number, cli_count,
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
        microkit_notify(clients[cli_id].ch);
    }

    return driver_notify;
}

static void handle_clients()
{
    bool driver_notify = false;
    for (int i = 0; i < BLK_NUM_CLIENTS; i++) {
        if (handle_client(i)) {
            driver_notify = true;
        }
    }

    if (driver_notify) {
        microkit_notify(DRIVER_CH);
    }
}

void notified(microkit_channel ch)
{
    if (virt_status == VirtBringup) {
        if (ch != DRIVER_CH) {
            /* ignore client requests */
            return;
        }

        bool done = policy_init();
        if (done) {
            /* keep in sync with handle_driver_state() */
            virt_status = VirtReady;
            notify_clients_state();
        };

        return;
    } else if (virt_status == VirtInactive) {
        // TODO: Respond with GONE?
        return;
    }

    if (ch == DRIVER_CH) {
        handle_driver_queue();
        handle_clients();
    } else {
        handle_clients();
    }
}
