/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>

#include <blk_config.h>

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("BLK DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("BLK DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define PAGE_SIZE_4K 0x1000
#define SECTOR_SIZE PAGE_SIZE_4K

#ifndef SERIAL_NUMBER
#define SERIAL_NUMBER "sddf_ramdisk0"
#endif

#define VIRT_CH 0

blk_storage_info_t *blk_storage_info;
blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;
static blk_queue_handle_t blk_queue;

/* Need this as our ramdisk isn't a DMA device so we need to convert DMA addresses to offsets in ramdisk. */
/* NOTE: This ramdisk implementation current assume only 1 client! */
uintptr_t blk_client0_data_paddr;
uintptr_t blk_client0_data_vaddr;

extern uintptr_t _ramdisk_begin;
extern uintptr_t _ramdisk_end;

bool check_cli_data_paddr_bound(uintptr_t cli_paddr) {
    if (cli_paddr >= blk_client0_data_paddr && cli_paddr < (blk_client0_data_paddr + BLK_REGION_SIZE)) {
        return true;
    } else {
        return false;
    }
}

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
            /* Nothing to do. Requests are completed as they come in. */
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
    assert(!blk_storage_info->ready);

    /* Initialise device information. */
    sddf_strncpy(blk_storage_info->serial_number, SERIAL_NUMBER, BLK_MAX_SERIAL_NUMBER);
    blk_storage_info->read_only = false;

    /* Optimal block size same as sector size. */
    blk_storage_info->sector_size = SECTOR_SIZE;
    blk_storage_info->block_size = 1;

    /* NOTE: Last block unusable if the total bytes size is not divisible by the sector size. */
    blk_storage_info->capacity = (uint64_t) ((_ramdisk_begin - _ramdisk_end) / SECTOR_SIZE);

    /* Our ramdisk has one platter and one reading head. */
    blk_storage_info->cylinders = 1;
    blk_storage_info->heads = 1;
    blk_storage_info->blocks = blk_storage_info->capacity;

    blk_queue_init(&blk_queue, blk_req_queue, blk_resp_queue, BLK_QUEUE_CAPACITY_DRIV);
    __atomic_store_n(&blk_storage_info->ready, true, __ATOMIC_RELEASE);
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
