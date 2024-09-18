/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "virt.h"

#include <sddf/blk/msdos_mbr.h>
#include <sddf/blk/queue.h>
#include <sddf/util/fsmalloc.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>

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

void partitions_init(void)
{
    if (msdos_mbr.signature != MSDOS_MBR_SIGNATURE) {
        LOG_BLK_VIRT_ERR("Invalid MBR signature\n");
        return;
    }

    /* Count the partitions the disk has and whether they are valid for sDDF. */
    int num_partitions = 0;
    for (int i = 0; i < MSDOS_MBR_MAX_PRIMARY_PARTITIONS; i++) {
        if (msdos_mbr.partitions[i].type == MSDOS_MBR_PARTITION_TYPE_EMPTY) {
            continue;
        } else {
            num_partitions++;
        }

        if (msdos_mbr.partitions[i].lba_start % (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE) != 0) {
            LOG_BLK_VIRT_ERR("Partition %d start sector %d not aligned to sDDF transfer size\n", i,
                             msdos_mbr.partitions[i].lba_start);
            return;
        }
    }

    if (num_partitions < BLK_NUM_CLIENTS) {
        LOG_BLK_VIRT_ERR("Not enough partitions to assign to clients\n");
        return;
    }

    /* Assign metadata for each client partition */
    for (int client = 0; client < BLK_NUM_CLIENTS; client++) {
        size_t client_partition = blk_partition_mapping[client];
        if (client_partition >= num_partitions) {
            LOG_BLK_VIRT_ERR("Invalid client partition mapping for client %d: %zu\n", client, client_partition);
            return;
        }

        /* We have a valid partition now. */
        clients[client].start_sector = msdos_mbr.partitions[client_partition].lba_start;
        clients[client].sectors = msdos_mbr.partitions[client_partition].sectors;
    }

    for (int i = 0; i < BLK_NUM_CLIENTS; i++) {
        blk_storage_info_t *curr_blk_config = blk_virt_cli_config_info(blk_config, i);
        curr_blk_config->sector_size = blk_config_driver->sector_size;
        curr_blk_config->capacity = clients[i].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
        curr_blk_config->read_only = blk_config_driver->read_only;
    }
}

int get_drv_block_number(uint32_t cli_block_number, uint16_t cli_count, int cli_id, uint32_t *drv_block_number)
{
    uint32_t block_number = cli_block_number
                          + (clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE));

    // Check if client request is within its allocated bounds
    unsigned long client_sectors = clients[cli_id].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
    unsigned long client_start_sector = clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
    if (block_number < client_start_sector || block_number + cli_count > client_start_sector + client_sectors) {
        return -1;
    }

    *drv_block_number = block_number;

    return 0;
}

bool handle_mbr_reply(void)
{
    int err;

    if (blk_queue_empty_resp(&drv_h)) {
        LOG_BLK_VIRT_ERR("Notified by driver but queue is empty, expecting a response to READ into sector 0\n");
        return false;
    }

    blk_resp_status_t drv_status;
    uint16_t drv_success_count;
    uint32_t drv_resp_id;
    err = blk_dequeue_resp(&drv_h, &drv_status, &drv_success_count, &drv_resp_id);
    assert(!err);

    if (drv_resp_id != state.mbr_req_id) {
        /* was for some other request. */
        LOG_BLK_VIRT_ERR("other request! lost!\n");
        return false;
    }
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
    fsmalloc_free(&fsmalloc, state.mbr_req_addr, mbr_req_count);

    return true;
}

void request_mbr(void)
{
    int err = fsmalloc_alloc(&fsmalloc, &state.mbr_req_addr, mbr_req_count);
    assert(!err);

    err = ialloc_alloc(&ialloc, &state.mbr_req_id);
    assert(!err);
    err = blk_enqueue_req(&drv_h, BLK_REQ_READ, BLK_DRIV_TO_PADDR(state.mbr_req_addr), 0x0, mbr_req_count,
                          state.mbr_req_id);
    assert(!err);

    microkit_deferred_notify(DRIVER_BLK_QUEUE_CH);
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
