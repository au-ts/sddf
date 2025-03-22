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
static client_t clients[SDDF_BLK_MAX_CLIENTS];

/* MS-DOS Master boot record */
static struct msdos_mbr msdos_mbr;

static const int mbr_req_count = 1;
static struct {
    bool sent_request;
    uintptr_t mbr_req_addr;
    uint32_t mbr_req_id;
} state;

static void partitions_dump()
{
    sddf_dprintf("the following partitions exist:\n");
    for (int i = 0; i < MSDOS_MBR_MAX_PRIMARY_PARTITIONS; i++) {
        sddf_dprintf("partition %d: type: 0x%hhx", i, msdos_mbr.partitions[i].type);
        if (msdos_mbr.partitions[i].type == MSDOS_MBR_PARTITION_TYPE_EMPTY) {
            sddf_dprintf(" (empty)\n");
        } else {
            sddf_dprintf("\n");
        }
    }
}

static void partitions_init()
{
    if (msdos_mbr.signature != MSDOS_MBR_SIGNATURE) {
        LOG_BLK_VIRT_ERR("Invalid MBR signature\n");
        return;
    }

    /* Validate partition and assign to client */
    for (int i = 0; i < config.num_clients; i++) {
        blk_virt_config_client_t *client = &config.clients[i];
        size_t client_partition = client->partition;

        if (client_partition >= MSDOS_MBR_MAX_PRIMARY_PARTITIONS
            || msdos_mbr.partitions[client_partition].type == MSDOS_MBR_PARTITION_TYPE_EMPTY) {
            /* Partition does not exist */
            LOG_BLK_VIRT_ERR(
                "Invalid client partition mapping for client %d: partition: %zu, partition does not exist\n", i,
                client_partition);
            partitions_dump();
            return;
        }

        if (msdos_mbr.partitions[client_partition].lba_start % (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE) != 0) {
            /* Partition start sector is not aligned to sDDF transfer size */
            LOG_BLK_VIRT_ERR("Partition %d start sector %d not aligned to sDDF transfer size\n", (int)client_partition,
                             msdos_mbr.partitions[client_partition].lba_start);
            return;
        }

        /* We have a valid partition now. */
        clients[i].start_sector = msdos_mbr.partitions[client_partition].lba_start;
        clients[i].sectors = msdos_mbr.partitions[client_partition].sectors;

        blk_storage_info_t *client_storage_info = client->conn.storage_info.vaddr;
        blk_storage_info_t *driver_storage_info = config.driver.conn.storage_info.vaddr;
        client_storage_info->sector_size = driver_storage_info->sector_size;
        client_storage_info->capacity = clients[i].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
        client_storage_info->read_only = driver_storage_info->read_only;
        __atomic_store_n(&client_storage_info->ready, true, __ATOMIC_RELEASE);
    }
}

static void request_mbr()
{
    int err = 0;
    uintptr_t mbr_paddr = config.driver.data.io_addr;
    state.mbr_req_addr = (uintptr_t)config.driver.data.region.vaddr;

    err = ialloc_alloc(&ialloc, &state.mbr_req_id);
    assert(!err);

    /* Virt-to-driver data region needs to be big enough to transfer MBR data */
    assert(config.driver.data.region.size >= BLK_TRANSFER_SIZE);
    err = blk_enqueue_req(&drv_h, BLK_REQ_READ, mbr_paddr, 0, 1, state.mbr_req_id);
    assert(!err);

    microkit_deferred_notify(config.driver.conn.id);
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
#ifdef CONFIG_ARCH_ARM
    seL4_ARM_VSpace_Invalidate_Data(3, state.mbr_req_addr, state.mbr_req_addr + (BLK_TRANSFER_SIZE * mbr_req_count));
#endif
    sddf_memcpy(&msdos_mbr, (void *)state.mbr_req_addr, sizeof(struct msdos_mbr));

    return true;
}

blk_resp_status_t get_drv_block_number(uint64_t cli_block_number, uint16_t cli_count, int cli_id,
                                       uint64_t *drv_block_number)
{
    uint64_t block_number = cli_block_number
                          + (clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE));

    unsigned long client_sectors = clients[cli_id].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
    unsigned long client_start_sector = clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
    if (block_number < client_start_sector || block_number + cli_count > client_start_sector + client_sectors) {
        /* Requested block number out of bounds */
        LOG_BLK_VIRT_ERR("client %d request for block %lu is out of bounds\n", cli_id, cli_block_number);
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
