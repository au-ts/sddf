/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>

#define VIRT_CH 0

blk_storage_info_t *blk_storage_info;
blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;

uintptr_t requests_paddr;
uintptr_t requests_vaddr;

static blk_queue_handle_t blk_queue;

char *ram_disk;

void handle_request()
{
    while (!blk_queue_empty_req(&blk_queue)) {
        blk_req_code_t req_code;
        uintptr_t phys_addr;
        uint32_t block_number;
        uint16_t count;
        uint32_t id;
        int err = blk_dequeue_req(&blk_queue, &req_code, &phys_addr, &block_number, &count, &id);
        assert(!err);

        switch (req_code) {
        case BLK_REQ_READ:
            LOG_DRIVER("handling read request with physical address 0x%lx, block_number: 0x%x, count: 0x%x, id: 0x%x\n",
                       phys_addr, block_number, count, id);

            int err = blk_enqueue_resp(&blk_queue, BLK_RESP_OK, 0, id);
            assert(!err);
            microkit_notify(VIRT_CH);
            break;
        case BLK_REQ_WRITE: {
            LOG_DRIVER("handling write request with physical address 0x%lx, block_number: 0x%x, count: 0x%x, id: 0x%x\n",
                       phys_addr, block_number, count, id);

            int err = blk_enqueue_resp(&blk_queue, BLK_RESP_OK, 0, id);
            assert(!err);
            microkit_notify(VIRT_CH);
            break;
        }
        case BLK_REQ_FLUSH:
        case BLK_REQ_BARRIER: {
            /* Nothing to do. */
            int err = blk_enqueue_resp(&blk_queue, BLK_RESP_OK, 0, id);
            assert(!err);
            microkit_notify(VIRT_CH);
            break;
        }
        default:
            /* The virtualiser should have sanitised the request code and so we should never get here. */
            LOG_DRIVER_ERR("unsupported request code: 0x%x\n", req_code);
            break;
        }
    }
}

void init(void)
{
    blk_queue_init(&blk_queue, blk_req_queue, blk_resp_queue, QUEUE_SIZE);
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case VIRT_CH:
        handle_request();
        break;
    default:
        LOG_DRIVER_ERR("received notification from unknown channel: 0x%x\n", ch);
    }
}
