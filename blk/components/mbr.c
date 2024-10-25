/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "virt.h"

#include <sddf/blk/msdos_mbr.h>
#include <sddf/util/util.h>

/* Client specific info */
typedef struct client {
    uint32_t start_sector;
    uint32_t sectors;
} client_t;
static client_t clients[BLK_NUM_CLIENTS];

/* MS-DOS Master boot record */
static struct msdos_mbr msdos_mbr;

static const int mbr_req_count = 1;
static struct {
    bool sent_request;
    uintptr_t mbr_req_addr;
    uint32_t mbr_req_id;
} state;

static void partitions_init(void)
{
    if (msdos_mbr.signature != MSDOS_MBR_SIGNATURE) {
        LOG_BLK_VIRT_ERR("Invalid MBR signature\n");
        return;
    }

    /* Validate partition and assign to client */
    for (int client = 0; client < BLK_NUM_CLIENTS; client++) {
        size_t client_partition = blk_partition_mapping[client];

        if (msdos_mbr.partitions[client_partition].type == MSDOS_MBR_PARTITION_TYPE_EMPTY) {
            /* Partition does not exist */
            LOG_BLK_VIRT_ERR(
                "Invalid client partition mapping for client %d: partition: %zu, partition does not exist\n", client,
                client_partition);
            return;
        }

        if (msdos_mbr.partitions[client_partition].lba_start % (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE) != 0) {
            /* Partition start sector is not aligned to sDDF transfer size */
            LOG_BLK_VIRT_ERR("Partition %d start sector %d not aligned to sDDF transfer size\n", (int)client_partition,
                             msdos_mbr.partitions[client_partition].lba_start);
            return;
        }

        /* We have a valid partition now. */
        clients[client].start_sector = msdos_mbr.partitions[client_partition].lba_start;
        clients[client].sectors = msdos_mbr.partitions[client_partition].sectors;
    }

    for (int i = 0; i < BLK_NUM_CLIENTS; i++) {
        blk_storage_info_t *cli_storage_info = blk_virt_cli_storage_info(blk_client_storage_info, i);
        cli_storage_info->sector_size = blk_driver_storage_info->sector_size;
        cli_storage_info->capacity = clients[i].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
        cli_storage_info->read_only = false; /* TODO */
        __atomic_store_n(&cli_storage_info->ready, true, __ATOMIC_RELEASE);
    }
}

static void request_mbr()
{
    int err = 0;
    uintptr_t mbr_paddr = blk_data_paddr_driver;
    state.mbr_req_addr = blk_driver_data;

    err = ialloc_alloc(&ialloc, &state.mbr_req_id);
    assert(!err);

    /* Virt-to-driver data region needs to be big enough to transfer MBR data */
    assert(BLK_DATA_REGION_SIZE_DRIV >= BLK_TRANSFER_SIZE);
    err = blk_enqueue_req(&drv_h, BLK_REQ_READ, mbr_paddr, 0, 1, state.mbr_req_id);
    assert(!err);

    microkit_deferred_notify(DRIVER_BLK_QUEUE_CH);
}

static bool handle_mbr_reply()
{
    int err = 0;
    if (blk_queue_empty_resp(&drv_h)) {
        LOG_BLK_VIRT(
            "Notified by driver but queue is empty, expecting a response to a BLK_REQ_READ request into sector 0\n");
        return false;
    }

    blk_resp_status_t drv_status;
    uint16_t drv_success_count;
    uint32_t drv_resp_id;
    err = blk_dequeue_resp(&drv_h, &drv_status, &drv_success_count, &drv_resp_id);
    assert(!err);

    err = ialloc_free(&ialloc, state.mbr_req_id);
    assert(!err);

    if (drv_status != BLK_RESP_OK) {
        LOG_BLK_VIRT_ERR("Failed to read sector 0 from driver\n");
        return false;
    }

    /* TODO: This is a raw seL4 system call because Microkit does not (currently)
     * include a corresponding libmicrokit API. */
    seL4_ARM_VSpace_Invalidate_Data(3, state.mbr_req_addr, state.mbr_req_addr + (BLK_TRANSFER_SIZE * mbr_req_count));
    sddf_memcpy(&msdos_mbr, (void *)state.mbr_req_addr, sizeof(struct msdos_mbr));

    return true;
}

blk_resp_status_t get_drv_block_number(uint32_t cli_block_number, uint16_t cli_count, int cli_id,
                                       uint32_t *drv_block_number)
{
    uint32_t block_number = cli_block_number
                          + (clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE));

    unsigned long client_sectors = clients[cli_id].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
    unsigned long client_start_sector = clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
    if (block_number < client_start_sector || block_number + cli_count > client_start_sector + client_sectors) {
        /* Requested block number out of bounds */
        LOG_BLK_VIRT_ERR("client %d request for block %d is out of bounds\n", cli_id, cli_block_number);
        return BLK_RESP_ERR_INVALID_PARAM;
    }

    *drv_block_number = block_number;

    return BLK_RESP_OK;
}

bool policy_init(void)
{
    if (state.sent_request == false) {
        request_mbr();
        state.sent_request = true;

        return false;
    }

    bool success = handle_mbr_reply();
    if (!success) {
        return false;
    }

    partitions_init();

    return true;
}

void policy_reset(void)
{
    sddf_memset(&state, 0x0, sizeof(state));
    sddf_memset(clients, 0x0, sizeof(clients));
    sddf_memset(&msdos_mbr, 0x0, sizeof(msdos_mbr));
}
