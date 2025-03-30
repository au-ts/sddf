/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "virt.h"
#include "msdos_mbr.h"
#include "gpt.h"

#include <sddf/util/cache.h>
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
    /* Whether or not we have sent the initial request to the driver for the MBR metadata block. */
    bool sent_request;
    /* Request info associated with the MBR metadata block request, valid after sent_request is true */
    uintptr_t req_addr;
    uint32_t req_id;
} mbr_state;

/* GPT metadata */
/* There are usually 1 (Protective MBR) + 1 (partition header) + 32 (partition table entries) sectors at the
 * start of the disk in total, but the size of entry could be different in some cases. */
static struct {
    struct gpt_partition_header *header;
    struct gpt_partition_entry *table;
    struct gpt_partition_header *mirror_header;
    struct gpt_partition_entry *mirror_table;
    uint32_t table_size;
} gpt_meta;

static struct {
    /* Whether or not we have started the requests for GPT metadata blocks. */
    bool sent_request;
    uintptr_t req_addr;
    uint32_t req_id;
    uint32_t req_cnt;
    uintptr_t mirror_req_addr;
    uint32_t mirror_req_id;
    uint32_t mirror_req_cnt;
    bool partition_table_ready;
    bool mirror_partition_table_ready;
} gpt_state;

static void mbr_partitions_dump()
{
    sddf_dprintf("the following MBR partitions exist:\n");
    for (int i = 0; i < MSDOS_MBR_MAX_PRIMARY_PARTITIONS; i++) {
        sddf_dprintf("      partition %d: type: 0x%hhx", i, msdos_mbr.partitions[i].type);
        if (msdos_mbr.partitions[i].type == MSDOS_MBR_PARTITION_TYPE_EMPTY) {
            sddf_dprintf(" (empty)\n");
        } else {
            sddf_dprintf("\n");
        }
    }
}

static void gpt_partitions_dump()
{
    sddf_dprintf("the following GPT partitions exist:\n");
    for (int i = 0; i < GPT_MAX_PARTITIONS; i++) {
        /* If no lba_start addr, then do not dump the partition as it is non-existent. */
        if (gpt_meta.table[i].lba_start != 0) {
            sddf_dprintf("      partition %d, lba_start: 0x%lx, name: %s\n", i, gpt_meta.table[i].lba_start,
                         gpt_meta.table[i].name);
        }
    }
}

static bool gpt_partitions_init()
{
    for (int i = 0; i < config.num_clients; i++) {
        blk_virt_config_client_t *client = &config.clients[i];
        size_t client_partition = client->partition;
        if (gpt_meta.table[client_partition].lba_start == 0) {
            /* Partition does not exist */
            LOG_BLK_VIRT_ERR(
                "Invalid client partition mapping for client %d: partition: %zu, partition does not exist\n", i,
                client_partition);
            gpt_partitions_dump();
            return false;
        }
        clients[i].start_sector = gpt_meta.table[client_partition].lba_start;
        clients[i].sectors = gpt_meta.table[client_partition].lba_end - gpt_meta.table[client_partition].lba_start + 1;

        blk_storage_info_t *client_storage_info = client->conn.storage_info.vaddr;
        blk_storage_info_t *driver_storage_info = config.driver.conn.storage_info.vaddr;
        client_storage_info->sector_size = driver_storage_info->sector_size;
        client_storage_info->capacity = clients[i].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
        client_storage_info->read_only = driver_storage_info->read_only;
        __atomic_store_n(&client_storage_info->ready, true, __ATOMIC_RELEASE);
    }

    return true;
}

uint32_t gpt_calc_crc32(const uint8_t *buffer, uint32_t len)
{
    int i, j;
    uint32_t byte, crc, mask;

    i = 0;
    crc = 0xFFFFFFFF;
    for (i = 0; i < len; i++) {
        byte = buffer[i];            // Get next byte.
        crc = crc ^ byte;
        for (j = 7; j >= 0; j--) {    // Do eight times.
            mask = -(crc & 1);
            crc = (crc >> 1) ^ (0xEDB88320 & mask);
        }
    }
    return ~crc;
}

static bool gpt_validate_partitions()
{
    int err = 0;
    if (blk_queue_empty_resp(&drv_h)) {
        LOG_BLK_VIRT("Notified by driver but queue is empty, expecting a response to a BLK_REQ_READ request for GPT "
                     "partition entries\n");
        return false;
    }

    blk_resp_status_t drv_status;
    uint16_t drv_success_count;
    uint32_t gpt_resp_id;

    /* Two responses could be notified only once */
    while (!blk_queue_empty_resp(&drv_h)) {
        err = blk_dequeue_resp(&drv_h, &drv_status, &drv_success_count, &gpt_resp_id);
        assert(!err);

        err = ialloc_free(&ialloc, gpt_resp_id);
        assert(!err);

        if (drv_status != BLK_RESP_OK) {
            LOG_BLK_VIRT_ERR("Failed to read partition table from driver\n");
            return false;
        }

        if (gpt_resp_id == gpt_state.req_id) {
            // Validate the signature in partition header
            if (sddf_strcmp(gpt_meta.header->signature, GPT_HEADER_SIGNATURE)) {
                LOG_BLK_VIRT_ERR("Invalid GPT signature\n");
                return false;
            }

            // Validate the header checksum
            uint32_t reserved_crc32 = gpt_meta.header->crc32_header;
            gpt_meta.header->crc32_header = 0;              // checksum field is zeroed for calculation
            uint32_t crc32_header = gpt_calc_crc32((uint8_t *)gpt_meta.header, 0x5C);
            if (crc32_header != reserved_crc32) {
                LOG_BLK_VIRT_ERR("CRC32 checksum is incorrect.\n");
                return false;
            }
            gpt_meta.header->crc32_header = reserved_crc32; // Recover the checksum field

            cache_clean_and_invalidate(gpt_state.req_addr,
                                       gpt_state.req_addr + (BLK_TRANSFER_SIZE * gpt_state.req_cnt));

            uint32_t crc32_entry_array = gpt_calc_crc32((uint8_t *)gpt_meta.table, gpt_meta.table_size);
            if (crc32_entry_array != gpt_meta.header->crc32_entry_array) {
                LOG_BLK_VIRT_ERR("CRC32 checksum of partition entry array is incorrect.\n");
                return false;
            }

            gpt_state.partition_table_ready = true;

        } else if (gpt_resp_id == gpt_state.mirror_req_id) {
            cache_clean_and_invalidate(gpt_state.mirror_req_addr,
                                       gpt_state.mirror_req_addr + (BLK_TRANSFER_SIZE * gpt_state.mirror_req_cnt));
            assert(!err);

            gpt_meta.mirror_header = (struct gpt_partition_header *)(gpt_state.mirror_req_addr
                                                                     + gpt_state.mirror_req_cnt * BLK_TRANSFER_SIZE
                                                                     - GPT_SECTOR_SIZE);
            // Validate the signature in mirror header
            if (sddf_strcmp(gpt_meta.mirror_header->signature, GPT_HEADER_SIGNATURE)) {
                LOG_BLK_VIRT_ERR("Invalid GPT signature in mirror partition header\n");
                return false;
            }

            // Validate the CRC32 checksum in mirror header
            // mirror header is located at the back of the disk
            uint32_t reserved_crc32 = gpt_meta.mirror_header->crc32_header;
            gpt_meta.mirror_header->crc32_header = 0;              // checksum field is zeroed for calculation
            uint32_t crc32_header = gpt_calc_crc32((uint8_t *)gpt_meta.mirror_header, 0x5C);
            if (crc32_header != reserved_crc32) {
                LOG_BLK_VIRT_ERR("mirror CRC32 checksum is incorrect.\n");
                return false;
            }
            gpt_meta.mirror_header->crc32_header = reserved_crc32; // Recover the checksum field

            // Validate mirror partition table
            // mirror table is before the mirror header
            uint32_t table_offset = gpt_state.mirror_req_cnt * BLK_TRANSFER_SIZE - gpt_meta.table_size
                                  - GPT_SECTOR_SIZE;
            gpt_meta.mirror_table = (struct gpt_partition_entry *)(gpt_state.mirror_req_addr + table_offset);
            uint32_t crc32_mirror_entry_array = gpt_calc_crc32((uint8_t *)gpt_meta.mirror_table, gpt_meta.table_size);
            if (crc32_mirror_entry_array != gpt_meta.mirror_header->crc32_entry_array) {
                LOG_BLK_VIRT_ERR("CRC32 checksum of partition entry array is incorrect.\n");
                return false;
            }

            gpt_state.mirror_partition_table_ready = true;
        }
    }

    if (gpt_state.partition_table_ready && gpt_state.mirror_partition_table_ready) {
        // Compare key fields of partition header and backup header
        assert(gpt_meta.header->revision == gpt_meta.mirror_header->revision);
        assert(gpt_meta.header->header_size == gpt_meta.mirror_header->header_size);
        for (int i = 0; i < 16; i++) {
            assert(gpt_meta.header->guid[i] == gpt_meta.mirror_header->guid[i]);
        }
        assert(gpt_meta.header->lba_header == gpt_meta.mirror_header->lba_alt_header);
        assert(gpt_meta.header->lba_alt_header == gpt_meta.mirror_header->lba_header);
        assert(gpt_meta.header->lba_start = gpt_meta.mirror_header->lba_start);
        assert(gpt_meta.header->num_entries = gpt_meta.mirror_header->num_entries);
        assert(gpt_meta.header->entry_size = gpt_meta.mirror_header->entry_size);
        assert(gpt_meta.header->crc32_entry_array = gpt_meta.mirror_header->crc32_entry_array);

        return true;
    }
    return false;
}

static bool mbr_partitions_init(void)
{
    if (msdos_mbr.signature != MSDOS_MBR_SIGNATURE) {
        LOG_BLK_VIRT_ERR("Invalid MBR signature\n");
        return false;
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
            mbr_partitions_dump();
            return false;
        }

        if (msdos_mbr.partitions[client_partition].lba_start % (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE) != 0) {
            /* Partition start sector is not aligned to sDDF transfer size */
            LOG_BLK_VIRT_ERR("Partition %d start sector %d not aligned to sDDF transfer size\n", (int)client_partition,
                             msdos_mbr.partitions[client_partition].lba_start);
            return false;
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
    return true;
}

static void mbr_request()
{
    int err = 0;
    uintptr_t mbr_paddr = config.driver.data.io_addr;
    mbr_state.req_addr = (uintptr_t)config.driver.data.region.vaddr;

    err = ialloc_alloc(&ialloc, &mbr_state.req_id);
    assert(!err);

    /* Virt-to-driver data region needs to be big enough to transfer MBR data */
    assert(config.driver.data.region.size >= BLK_TRANSFER_SIZE);
    err = blk_enqueue_req(&drv_h, BLK_REQ_READ, mbr_paddr, 0, 1, mbr_state.req_id);
    assert(!err);

    microkit_deferred_notify(config.driver.conn.id);

    mbr_state.sent_request = true;
}

/* Process response for MBR metadata.
 * Returns true if valid MBR.
 * Return false if invalid MBR or GPT disk.
 */
static bool mbr_handle_response()
{
    /* Should not get here without the initial metadata request. */
    assert(mbr_state.sent_request);

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

    err = ialloc_free(&ialloc, mbr_state.req_id);
    assert(!err);

    if (drv_status != BLK_RESP_OK) {
        LOG_BLK_VIRT_ERR("Failed to read sector 0 from driver\n");
        return false;
    }

    cache_clean_and_invalidate(mbr_state.req_addr, mbr_state.req_addr + (BLK_TRANSFER_SIZE * mbr_req_count));
    sddf_memcpy(&msdos_mbr, (void *)mbr_state.req_addr, sizeof(struct msdos_mbr));

    /* There is only one partition entry in Protective MBR of the GPT partition schema */
    if (msdos_mbr.partitions[0].type == MSDOS_MBR_PARTITION_TYPE_GPT) {
        LOG_BLK_VIRT("Protective MBR of GPT is detected\n");

        /* Save the primary GPT header, and validate the header in gpt_validate_partitionsk() */
        gpt_meta.header = (struct gpt_partition_header *)(mbr_state.req_addr + GPT_SECTOR_SIZE);
        gpt_meta.table_size = gpt_meta.header->num_entries * gpt_meta.header->entry_size;

        /* Copy the first two sectors of partition entries to the table */
        gpt_meta.table = (struct gpt_partition_entry *)(mbr_state.req_addr + GPT_SECTOR_SIZE * 2);

        /* Request for the blocks containing the rest of partition entries */
        uint32_t gpt_req_id = 0;
        err = ialloc_alloc(&ialloc, &gpt_req_id);
        assert(!err);
        uint32_t meta_blk_cnt = (GPT_SECTOR_SIZE * 2 + BLK_TRANSFER_SIZE - 1 + gpt_meta.table_size) / BLK_TRANSFER_SIZE;
        gpt_state.req_addr = (uintptr_t)config.driver.data.region.vaddr + BLK_TRANSFER_SIZE;
        gpt_state.req_id = gpt_req_id;
        gpt_state.req_cnt = meta_blk_cnt - 1;
        err = blk_enqueue_req(&drv_h, BLK_REQ_READ, (uintptr_t)config.driver.data.io_addr + BLK_TRANSFER_SIZE, 1,
                              meta_blk_cnt - 1, gpt_req_id);
        assert(!err);

        /* Request for mirror of partition table and header */
        err = ialloc_alloc(&ialloc, &gpt_req_id);
        assert(!err);

        uint32_t meta_mirror_blk_cnt = (GPT_SECTOR_SIZE * 1 + BLK_TRANSFER_SIZE - 1 + gpt_meta.table_size)
                                     / BLK_TRANSFER_SIZE;
        uint32_t mirror_blk_start = (gpt_meta.header->lba_alt_header - gpt_meta.table_size / GPT_SECTOR_SIZE)
                                  / (BLK_TRANSFER_SIZE / GPT_SECTOR_SIZE);
        gpt_state.mirror_req_addr = (uintptr_t)config.driver.data.region.vaddr + BLK_TRANSFER_SIZE * meta_blk_cnt;
        gpt_state.mirror_req_id = gpt_req_id;
        gpt_state.mirror_req_cnt = meta_mirror_blk_cnt;
        err = blk_enqueue_req(&drv_h, BLK_REQ_READ,
                              (uintptr_t)config.driver.data.io_addr + BLK_TRANSFER_SIZE * meta_blk_cnt,
                              mirror_blk_start, meta_mirror_blk_cnt, gpt_req_id);
        assert(!err);
        gpt_state.sent_request = true;

        microkit_deferred_notify(config.driver.conn.id);
        return false;
    }

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

bool virt_partition_init(void)
{
    if (!mbr_state.sent_request) {
        mbr_request();
        return false;
    }

    bool success = false;

    if (gpt_state.sent_request) {
        /* need to validate partition header and table of a GPT disk */
        success = gpt_validate_partitions();
        if (success) {
            success = gpt_partitions_init();
        }
        return success;
    }

    success = mbr_handle_response();
    if (success) {
        success = mbr_partitions_init();
    }

    return success;
}
