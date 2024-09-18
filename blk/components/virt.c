/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "virt.h"

#include <microkit.h>
#include <sddf/util/cache.h>
#include <sddf/util/printf.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>

#include "blk_config.h"

#define BLK_NUM_BUFFERS_DRIV (BLK_DATA_REGION_SIZE_DRIV / BLK_TRANSFER_SIZE)

#define REQBK_SIZE BLK_QUEUE_SIZE_DRIV

blk_storage_info_t *blk_config_driver;
blk_req_queue_t *blk_req_queue_driver;
blk_resp_queue_t *blk_resp_queue_driver;
uintptr_t blk_data_driver;
uintptr_t blk_data_driver_paddr;

blk_storage_info_t *blk_config;
blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;
/* The start of client data regions. */
uintptr_t blk_client_data_start;

blk_queue_handle_t drv_h;

/* Client specific info */
typedef struct client {
    blk_queue_handle_t queue_h;
    microkit_channel queue_ch;
    microkit_channel state_ch;
} client_t;
client_t clients[BLK_NUM_CLIENTS];


/* Fixed size memory allocator */
fsmalloc_t fsmalloc;
static bitarray_t fsmalloc_avail_bitarr;
static word_t fsmalloc_avail_bitarr_words[roundup_bits2words64(BLK_NUM_BUFFERS_DRIV)];

/* Bookkeeping struct per request */
typedef struct reqbk {
    uint32_t cli_id;
    uint32_t cli_req_id;
    uintptr_t cli_addr;
    uintptr_t drv_addr;
    uint16_t count;
    blk_req_code_t code;
} reqbk_t;
static reqbk_t reqbk[REQBK_SIZE];

/* Index allocator for request bookkeep */
ialloc_t ialloc;
static uint32_t ialloc_idxlist[REQBK_SIZE];

static enum {
    VirtInactive,
    VirtBringup,
    VirtReady,
} virt_status;

static void handle_driver_state();

void init(void)
{
    // Initialise client queues
    for (int i = 0; i < BLK_NUM_CLIENTS; i++) {
        blk_req_queue_t *curr_req = blk_virt_cli_req_queue(blk_req_queue, i);
        blk_resp_queue_t *curr_resp = blk_virt_cli_resp_queue(blk_resp_queue, i);
        uint32_t queue_size = blk_virt_cli_queue_size(i);
        blk_queue_init(&clients[i].queue_h, curr_req, curr_resp, queue_size);

        clients[i].queue_ch = CLI_CH_BASE + (i * CLI_CH_STRIDE) + CLI_CH_BLK_QUEUE_IDX;
        clients[i].state_ch = CLI_CH_BASE + (i * CLI_CH_STRIDE) + CLI_CH_BLK_STATE_IDX;
    }

    // Initialise driver queue
    blk_queue_init(&drv_h, blk_req_queue_driver, blk_resp_queue_driver, BLK_QUEUE_SIZE_DRIV);

    // Initialise fixed size memory allocator and ialloc
    ialloc_init(&ialloc, ialloc_idxlist, REQBK_SIZE);
    fsmalloc_init(&fsmalloc, blk_data_driver, BLK_TRANSFER_SIZE, BLK_NUM_BUFFERS_DRIV, &fsmalloc_avail_bitarr,
                  fsmalloc_avail_bitarr_words, roundup_bits2words64(BLK_NUM_BUFFERS_DRIV));

    /* continued via ready notifications */
}

static void handle_driver_queue()
{
    blk_resp_status_t drv_status;
    uint16_t drv_success_count;
    uint32_t drv_resp_id;

    int err = 0;
    while (!blk_queue_empty_resp(&drv_h)) {
        err = blk_dequeue_resp(&drv_h, &drv_status, &drv_success_count, &drv_resp_id);
        assert(!err);

        reqbk_t cli_data = reqbk[drv_resp_id];
        err = ialloc_free(&ialloc, drv_resp_id);
        assert(!err);

        // Free bookkeeping data structures regardless of success or failure
        switch (cli_data.code) {
        case BLK_REQ_WRITE:
            fsmalloc_free(&fsmalloc, cli_data.drv_addr, cli_data.count);
            break;
        case BLK_REQ_READ:
            fsmalloc_free(&fsmalloc, cli_data.drv_addr, cli_data.count);
            break;
        case BLK_REQ_FLUSH:
            break;
        case BLK_REQ_BARRIER:
            break;
        }

        // Get the corresponding client queue handle
        blk_queue_handle_t h = clients[cli_data.cli_id].queue_h;

        // Drop response if client resp queue is full
        if (blk_queue_full_resp(&h)) {
            continue;
        }

        if (drv_status == BLK_RESP_OK) {
            switch (cli_data.code) {
            case BLK_REQ_READ:
                // Invalidate cache
                /* TODO: This is a raw seL4 system call because Microkit does not (currently)
                 * include a corresponding libmicrokit API. */
                seL4_ARM_VSpace_Invalidate_Data(3, cli_data.drv_addr, cli_data.drv_addr + (BLK_TRANSFER_SIZE * cli_data.count));
                // Copy data buffers from driver to client
                sddf_memcpy((void *)cli_data.cli_addr, (void *)cli_data.drv_addr, BLK_TRANSFER_SIZE * cli_data.count);
                err = blk_enqueue_resp(&h, BLK_RESP_OK, drv_success_count, cli_data.cli_req_id);
                assert(!err);
                break;
            case BLK_REQ_WRITE:
                err = blk_enqueue_resp(&h, BLK_RESP_OK, drv_success_count, cli_data.cli_req_id);
                assert(!err);
                break;
            case BLK_REQ_FLUSH:
            case BLK_REQ_BARRIER:
                err = blk_enqueue_resp(&h, BLK_RESP_OK, drv_success_count, cli_data.cli_req_id);
                assert(!err);
                break;
            }
        } else {
            // When more error conditions are added, this will need to be updated to a switch statement
            err = blk_enqueue_resp(&h, drv_status, drv_success_count, cli_data.cli_req_id);
            assert(!err);
        }

        // Notify corresponding client
        microkit_notify(clients[cli_data.cli_id].queue_ch);
    }
}

static void notify_clients_state()
{
    bool driver_ready = blk_storage_is_ready(blk_config_driver);
    for (int i = 0; i < BLK_NUM_CLIENTS; i++) {
        blk_storage_info_t *curr_blk_config = blk_virt_cli_config_info(blk_config, i);

        blk_storage_notify_ready(curr_blk_config, clients[i].state_ch, driver_ready);
    }
}

static void handle_driver_state()
{
    bool driver_ready = blk_storage_is_ready(blk_config_driver);

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

static void handle_client(int cli_id)
{
    blk_queue_handle_t h = clients[cli_id].queue_h;
    uintptr_t cli_data_base = blk_virt_cli_data_region(blk_client_data_start, cli_id);
    uint64_t cli_data_region_size = blk_virt_cli_data_region_size(cli_id);

    while (!blk_queue_empty_req(&h)) {
        int err;

        blk_req_code_t cli_code;
        uintptr_t cli_offset;
        uint32_t cli_block_number;
        uint16_t cli_count;
        uint32_t cli_req_id;

        err = blk_dequeue_req(&h, &cli_code, &cli_offset, &cli_block_number, &cli_count, &cli_req_id);
        assert(!err);

        uintptr_t drv_addr = 0;
        uint32_t drv_block_number;

        if (cli_code == BLK_REQ_READ || cli_code == BLK_REQ_WRITE) {
            err = get_drv_block_number(cli_block_number, cli_count, cli_id, &drv_block_number);
            if (err) {
                LOG_BLK_VIRT_ERR("client %d request for block %d is out of bounds\n", cli_id, cli_block_number);
                err = blk_enqueue_resp(&h, BLK_RESP_ERR_INVALID_PARAM, 0, cli_req_id);
                assert(!err);
                continue;
            }

            // Check if client request offset is within its allocated bounds and is aligned to transfer size
            if (cli_offset % BLK_TRANSFER_SIZE != 0 || (cli_offset + BLK_TRANSFER_SIZE * cli_count) > cli_data_region_size) {
                LOG_BLK_VIRT_ERR("client %d request offset 0x%lx is invalid\n", cli_id, cli_offset);
                err = blk_enqueue_resp(&h, BLK_RESP_ERR_INVALID_PARAM, 0, cli_req_id);
                assert(!err);
                continue;
            }

            if (cli_count == 0) {
                LOG_BLK_VIRT_ERR("client %d requested zero blocks\n", cli_id);
                err = blk_enqueue_resp(&h, BLK_RESP_ERR_INVALID_PARAM, 0, cli_req_id);
                assert(!err);
                continue;
            }
        }

        switch (cli_code) {
        case BLK_REQ_READ:
            if (blk_queue_full_req(&drv_h) || ialloc_full(&ialloc) || fsmalloc_full(&fsmalloc, cli_count)) {
                continue;
            }
            // Allocate driver data buffers
            err = fsmalloc_alloc(&fsmalloc, &drv_addr, cli_count);
            assert(!err);
            break;
        case BLK_REQ_WRITE:
            if (blk_queue_full_req(&drv_h) || ialloc_full(&ialloc) || fsmalloc_full(&fsmalloc, cli_count)) {
                continue;
            }
            // Allocate driver data buffers
            err = fsmalloc_alloc(&fsmalloc, &drv_addr, cli_count);
            assert(!err);
            // Copy data buffers from client to driver
            sddf_memcpy((void *)drv_addr, (void *)(cli_offset + cli_data_base), BLK_TRANSFER_SIZE * cli_count);
            // Flush the cache
            cache_clean(drv_addr, drv_addr + (BLK_TRANSFER_SIZE * cli_count));
            break;
        case BLK_REQ_FLUSH:
        case BLK_REQ_BARRIER:
            if (blk_queue_full_req(&drv_h) || ialloc_full(&ialloc)) {
                continue;
            }
            break;
        default:
            /* Invalid request code given */
            LOG_BLK_VIRT_ERR("client %d gave an invalid request code %d\n", cli_id, cli_code);
            err = blk_enqueue_resp(&h, BLK_RESP_ERR_INVALID_PARAM, 0, cli_req_id);
            assert(!err);
            continue;
        }

        // Bookkeep client request and generate driver req ID
        reqbk_t cli_data = {cli_id, cli_req_id, cli_offset + cli_data_base, drv_addr, cli_count, cli_code};
        uint32_t drv_req_id = 0;
        err = ialloc_alloc(&ialloc, &drv_req_id);
        assert(!err);
        reqbk[drv_req_id] = cli_data;

        err = blk_enqueue_req(&drv_h, cli_code, BLK_DRIV_TO_PADDR(drv_addr), drv_block_number, cli_count, drv_req_id);
        assert(!err);
    }
}

void notified(microkit_channel ch)
{
    if (ch == DRIVER_BLK_STATE_CH) {
        handle_driver_state();
        return;
    }

    if (virt_status == VirtBringup) {
        if (ch != DRIVER_BLK_QUEUE_CH) {
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
        /* ??????  Respond with gone? */
        return;
    }

    if (ch == DRIVER_BLK_QUEUE_CH) {
        handle_driver_queue();
    } else {
        for (int i = 0; i < BLK_NUM_CLIENTS; i++) {
            handle_client(i);
        }
        microkit_deferred_notify(DRIVER_BLK_QUEUE_CH);
    }
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    return microkit_ppcall(DRIVER_BLK_STATE_CH, msginfo);
}
