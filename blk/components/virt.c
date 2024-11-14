/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/msdos_mbr.h>
#include <sddf/blk/gpt.h>
#include <sddf/util/cache.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>
#include <blk_config.h>

/* Uncomment this to enable debug logging */
// #define DEBUG_BLK_VIRT

#if defined(DEBUG_BLK_VIRT)
#define LOG_BLK_VIRT(...) do{ sddf_dprintf("BLK_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_BLK_VIRT(...) do{}while(0)
#endif
#define LOG_BLK_VIRT_ERR(...) do{ sddf_dprintf("BLK_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)


#define DRIVER_CH 0
#define CLI_CH_OFFSET 1

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
    uint32_t start_sector;
    uint32_t sectors;
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
static ialloc_t ialloc;
static uint32_t ialloc_idxlist[BLK_QUEUE_CAPACITY_DRIV];

/* MS-DOS Master boot record */
struct msdos_mbr msdos_mbr;

/* GPT metadata */
/* There are usually 1 (Protective MBR) + 1 (partition header) + 32 (partition table entries) sectors at the
 * start of the disk in total, but the size of entry could be different in some cases. */
struct gpt_partition_header *gpt_header;
struct gpt_partition_entry *gpt_table;
bool partition_table_ready = false;
struct gpt_partition_header *gpt_mirror_header;
struct gpt_partition_entry *gpt_mirror_table;
bool mirror_partition_table_ready = false;
uint32_t gpt_table_size;

/* The virtualiser is not initialised until we can read the MBR and populate the block device configuration. */
bool initialised = false;
bool gpt_table_requested = false;

static void gpt_partitions_init()
{
    int client;
    for (client = 0; client < BLK_NUM_CLIENTS; client++) {
        uint32_t entry_id = blk_partition_mapping[client];
        if (gpt_table[entry_id].lba_start == 0) {
            LOG_BLK_VIRT_ERR("Failed to assign non-exist partition %d to client %d\n", entry_id, client);
            return;
        }
        clients[client].start_sector = gpt_table[entry_id].lba_start;
        clients[client].sectors = gpt_table[entry_id].lba_end - gpt_table[entry_id].lba_start + 1;
    }

    for (int client = 0; client < BLK_NUM_CLIENTS; client++) {
        blk_storage_info_t *curr_blk_storage_info = blk_virt_cli_storage_info(blk_client_storage_info, client);
        curr_blk_storage_info->sector_size = blk_driver_storage_info->sector_size;
        curr_blk_storage_info->capacity = clients[client].sectors / (BLK_TRANSFER_SIZE / GPT_SECTOR_SIZE);
        curr_blk_storage_info->read_only = false;
        __atomic_store_n(&curr_blk_storage_info->ready, true, __ATOMIC_RELEASE);
    }
    initialised = true;
    return;
}

uint32_t calc_crc32(const uint8_t *buffer, uint32_t len)
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

static void validate_gpt_partitions()
{
    int err = 0;
    if (blk_queue_empty_resp(&drv_h)) {
        LOG_BLK_VIRT("Notified by driver but queue is empty, expecting a response to a BLK_REQ_READ request for GPT "
                     "partition entries\n");
        return;
    }

    blk_resp_status_t drv_status;
    uint16_t drv_success_count;
    uint32_t gpt_resp_id;

    /* Two responses could be notified only once */
    while (!blk_queue_empty_resp(&drv_h)) {
        err = blk_dequeue_resp(&drv_h, &drv_status, &drv_success_count, &gpt_resp_id);
        assert(!err);

        reqbk_t gpt_bk = reqsbk[gpt_resp_id];
        err = ialloc_free(&ialloc, gpt_resp_id);
        assert(!err);

        if (drv_status != BLK_RESP_OK) {
            LOG_BLK_VIRT_ERR("Failed to read partition table from driver\n");
            return;
        }

        /* TODO: This is a raw seL4 system call because Microkit does not (currently)
         * include a corresponding libmicrokit API. */

        if (gpt_bk.code == GPT_PARTITION_INFO_CODE) {
            // Validate the signature in partition header
            if (sddf_strcmp(gpt_header->signature, GPT_HEADER_SIGNATURE)) {
                LOG_BLK_VIRT_ERR("Invalid GPT signature\n");
                return;
            }

            // Validate the header checksum
            uint32_t reserved_crc32 = gpt_header->crc32_header;
            gpt_header->crc32_header = 0;              // checksum field is zeroed for calculation
            uint32_t crc32_header = calc_crc32((uint8_t *)gpt_header, 0x5C);
            if (crc32_header != reserved_crc32) {
                LOG_BLK_VIRT_ERR("CRC32 checksum is incorrect.\n");
                return;
            }
            gpt_header->crc32_header = reserved_crc32; // Recover the checksum field

            seL4_ARM_VSpace_Invalidate_Data(3, gpt_bk.vaddr, gpt_bk.vaddr + (BLK_TRANSFER_SIZE * gpt_bk.count));

            uint32_t crc32_entry_array = calc_crc32((uint8_t *)gpt_table, gpt_table_size);
            if (crc32_entry_array != gpt_header->crc32_entry_array) {
                LOG_BLK_VIRT_ERR("CRC32 checksum of partition entry array is incorrect.\n");
                return;
            }

            partition_table_ready = true;

        } else if (gpt_bk.code == GPT_PARTITION_INFO_MIRROR_CODE) {
            err = seL4_ARM_VSpace_Invalidate_Data(3, gpt_bk.vaddr, gpt_bk.vaddr + (BLK_TRANSFER_SIZE * gpt_bk.count));
            assert(!err);

            gpt_mirror_header = (struct gpt_partition_header *)(gpt_bk.vaddr + gpt_bk.count * BLK_TRANSFER_SIZE
                                                                - GPT_SECTOR_SIZE);
            // Validate the signature in mirror header
            if (sddf_strcmp(gpt_mirror_header->signature, GPT_HEADER_SIGNATURE)) {
                LOG_BLK_VIRT_ERR("Invalid GPT signature in mirror partition header\n");
                return;
            }

            // Validate the CRC32 checksum in mirror header
            // mirror header is locateda at the back of the disk
            uint32_t reserved_crc32 = gpt_mirror_header->crc32_header;
            gpt_mirror_header->crc32_header = 0;              // checksum field is zeroed for calculation
            uint32_t crc32_header = calc_crc32((uint8_t *)gpt_mirror_header, 0x5C);
            if (crc32_header != reserved_crc32) {
                LOG_BLK_VIRT_ERR("mirror CRC32 checksum is incorrect.\n");
                return;
            }
            gpt_mirror_header->crc32_header = reserved_crc32; // Recover the checksum field

            // Validate mirror partition table
            // mirror table is before the mirror header
            uint32_t table_offset = gpt_bk.count * BLK_TRANSFER_SIZE - gpt_table_size - GPT_SECTOR_SIZE;
            gpt_mirror_table = (struct gpt_partition_entry *)(gpt_bk.vaddr + table_offset);
            uint32_t crc32_mirror_entry_array = calc_crc32((uint8_t *)gpt_mirror_table, gpt_table_size);
            if (crc32_mirror_entry_array != gpt_mirror_header->crc32_entry_array) {
                LOG_BLK_VIRT_ERR("CRC32 checksum of partition entry array is incorrect.\n");
                return;
            }

            mirror_partition_table_ready = true;
        }
    }

    if (partition_table_ready && mirror_partition_table_ready) {
        // Compare key fields of partition header and backup header
        assert(gpt_header->revision == gpt_mirror_header->revision);
        assert(gpt_header->header_size == gpt_mirror_header->header_size);
        for (int i = 0; i < 16; i++) {
            assert(gpt_header->guid[i] == gpt_mirror_header->guid[i]);
        }
        assert(gpt_header->lba_header == gpt_mirror_header->lba_alt_header);
        assert(gpt_header->lba_alt_header == gpt_mirror_header->lba_header);
        assert(gpt_header->lba_start = gpt_mirror_header->lba_start);
        assert(gpt_header->num_entries = gpt_mirror_header->num_entries);
        assert(gpt_header->entry_size = gpt_mirror_header->entry_size);
        assert(gpt_header->crc32_entry_array = gpt_mirror_header->crc32_entry_array);

        gpt_partitions_init();
    }
}

static void mbr_partitions_init()
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
        blk_storage_info_t *curr_blk_storage_info = blk_virt_cli_storage_info(blk_client_storage_info, i);
        curr_blk_storage_info->sector_size = blk_driver_storage_info->sector_size;
        curr_blk_storage_info->capacity = clients[i].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
        curr_blk_storage_info->read_only = false;
        __atomic_store_n(&curr_blk_storage_info->ready, true, __ATOMIC_RELEASE);
    }

    initialised = true;
}

static void request_mbr()
{
    int err = 0;
    uintptr_t mbr_paddr = blk_data_paddr_driver;
    uintptr_t mbr_vaddr = blk_driver_data;

    uint32_t mbr_req_id = 0;
    err = ialloc_alloc(&ialloc, &mbr_req_id);
    assert(!err);
    reqsbk[mbr_req_id] = (reqbk_t) { 0, 0, mbr_vaddr, 1, 0 };

    /* Virt-to-driver data region needs to be big enough to transfer MBR data */
    assert(BLK_DATA_REGION_SIZE_DRIV >= BLK_TRANSFER_SIZE);
    err = blk_enqueue_req(&drv_h, BLK_REQ_READ, mbr_paddr, 0, 1, mbr_req_id);
    assert(!err);

    microkit_deferred_notify(DRIVER_CH);
}

static void handle_mbr_reply()
{
    int err = 0;
    if (blk_queue_empty_resp(&drv_h)) {
        LOG_BLK_VIRT(
            "Notified by driver but queue is empty, expecting a response to a BLK_REQ_READ request into sector 0\n");
        return;
    }

    blk_resp_status_t drv_status;
    uint16_t drv_success_count;
    uint32_t drv_resp_id;
    err = blk_dequeue_resp(&drv_h, &drv_status, &drv_success_count, &drv_resp_id);
    assert(!err);

    reqbk_t mbr_bk = reqsbk[drv_resp_id];
    err = ialloc_free(&ialloc, drv_resp_id);
    assert(!err);

    if (drv_status != BLK_RESP_OK) {
        LOG_BLK_VIRT_ERR("Failed to read sector 0 from driver\n");
        return;
    }

    /* TODO: This is a raw seL4 system call because Microkit does not (currently)
     * include a corresponding libmicrokit API. */
    seL4_ARM_VSpace_Invalidate_Data(3, mbr_bk.vaddr, mbr_bk.vaddr + (BLK_TRANSFER_SIZE * mbr_bk.count));
    sddf_memcpy(&msdos_mbr, (void *)mbr_bk.vaddr, sizeof(struct msdos_mbr));

    /* There is only one partition entry in Protective MBR of the GPT parition schema */
    if (msdos_mbr.partitions[0].type == MSDOS_MBR_PARTITION_TYPE_GPT) {
        LOG_BLK_VIRT("Protective MBR of GPT is detected\n");

        /* Save the primary GPT header, and validate the header in validate_gpt_partitions() */
        gpt_header = (struct gpt_partition_header *)(mbr_bk.vaddr + GPT_SECTOR_SIZE);
        gpt_table_size = gpt_header->num_entries * gpt_header->entry_size;

        /* Copy the first two sectors of partition entries to the table */
        gpt_table = (struct gpt_partition_entry *)(mbr_bk.vaddr + GPT_SECTOR_SIZE * 2);

        /* Request for the blocks containing the rest of partition entries */
        uint32_t gpt_req_id = 0;
        err = ialloc_alloc(&ialloc, &gpt_req_id);
        assert(!err);
        uint32_t meta_blk_cnt = (GPT_SECTOR_SIZE * 2 + BLK_TRANSFER_SIZE - 1 + gpt_table_size) / BLK_TRANSFER_SIZE;
        reqsbk[gpt_req_id] = (reqbk_t) { 0, 0, blk_driver_data + BLK_TRANSFER_SIZE, meta_blk_cnt - 1,
                                         GPT_PARTITION_INFO_CODE };
        err = blk_enqueue_req(&drv_h, BLK_REQ_READ, blk_data_paddr_driver + BLK_TRANSFER_SIZE, 1, meta_blk_cnt - 1,
                              gpt_req_id);
        assert(!err);

        /* Request for mirror of partition table and header */
        err = ialloc_alloc(&ialloc, &gpt_req_id);
        assert(!err);

        uint32_t meta_mirror_blk_cnt = (GPT_SECTOR_SIZE * 1 + BLK_TRANSFER_SIZE - 1 + gpt_table_size)
                                     / BLK_TRANSFER_SIZE;
        uint32_t mirror_blk_start = (gpt_header->lba_alt_header - gpt_table_size / GPT_SECTOR_SIZE)
                                  / (BLK_TRANSFER_SIZE / GPT_SECTOR_SIZE);
        reqsbk[gpt_req_id] = (reqbk_t) { 0, 0, blk_driver_data + BLK_TRANSFER_SIZE * meta_blk_cnt, meta_mirror_blk_cnt,
                                         GPT_PARTITION_INFO_MIRROR_CODE };
        err = blk_enqueue_req(&drv_h, BLK_REQ_READ, blk_data_paddr_driver + BLK_TRANSFER_SIZE * meta_blk_cnt,
                              mirror_blk_start, meta_mirror_blk_cnt, gpt_req_id);
        assert(!err);
        gpt_table_requested = true;

        microkit_deferred_notify(DRIVER_CH);
    } else {
        mbr_partitions_init();
    }
}

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

    request_mbr();
}

static void handle_driver()
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
        drv_block_number = cli_block_number + (clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE));

        blk_resp_status_t resp_status = BLK_RESP_ERR_UNSPEC;

        switch (cli_code) {
        case BLK_REQ_READ:
        case BLK_REQ_WRITE: {
            unsigned long client_sectors = clients[cli_id].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
            unsigned long client_start_sector = clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
            if (drv_block_number < client_start_sector || drv_block_number + cli_count > client_start_sector + client_sectors) {
                /* Requested block number out of bounds */
                LOG_BLK_VIRT_ERR("client %d request for block %d is out of bounds\n", cli_id, cli_block_number);
                resp_status = BLK_RESP_ERR_INVALID_PARAM;
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
    if (initialised == false) {
        if (gpt_table_requested) {
            validate_gpt_partitions();
        } else {
            handle_mbr_reply();
        }
        return;
    }

    if (ch == DRIVER_CH) {
        handle_driver();
        handle_clients();
    } else {
        handle_clients();
    }
}
