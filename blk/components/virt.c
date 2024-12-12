/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/blk/msdos_mbr.h>
#include <sddf/util/cache.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>

#define BLK_QUEUE_CAPACITY_DRIV 1024
#define MAX_NUM_CLIENTS 62

struct config_client {
    blk_req_queue_t *req_queue;
    blk_resp_queue_t *resp_queue;
    blk_storage_info_t *storage_info;
    uint64_t data_vaddr;
    uint64_t data_paddr;
    uint64_t data_size;
    uint64_t queue_capacity;
    uint32_t partition;
};

struct config_driver {
    blk_storage_info_t *storage_info;
    blk_req_queue_t *req_queue;
    blk_resp_queue_t *resp_queue;
    uint64_t data_vaddr;
    uint64_t data_paddr;
    uint64_t data_size;
};

struct config {
    uint64_t num_clients;
    struct config_driver driver;
    struct config_client clients[MAX_NUM_CLIENTS];
};

__attribute__((__section__(".blk_virt_config")))
struct config config;

/* Uncomment this to enable debug logging */
// #define DEBUG_BLK_VIRT

#if defined(DEBUG_BLK_VIRT)
#define LOG_BLK_VIRT(...) do{ sddf_dprintf("BLK_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_BLK_VIRT(...) do{}while(0)
#endif
#define LOG_BLK_VIRT_ERR(...) do{ sddf_dprintf("BLK_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

void config_debug_print(struct config *config) {
    LOG_BLK_VIRT("dumping config:\n");
    sddf_dprintf("num_clients: %lu\n", config->num_clients);
    sddf_dprintf("driver_storage_info: %p\n", config->driver.storage_info);
    sddf_dprintf("driver_req_queue: %p\n", config->driver.req_queue);
    sddf_dprintf("driver_resp_queue: %p\n", config->driver.resp_queue);
    sddf_dprintf("driver_data_vaddr: 0x%lx\n", config->driver.data_vaddr);
    sddf_dprintf("driver_data_paddr: 0x%lx\n", config->driver.data_paddr);
    for (int i = 0; i < config->num_clients; i++) {
        struct config_client *client = &config->clients[i];
        sddf_dprintf("client[%d]: req_queue: %p\n", i, client->req_queue);
        sddf_dprintf("client[%d]: resp_queue: %p\n", i, client->resp_queue);
    }
}


#define DRIVER_CH 0
#define CLI_CH_OFFSET 1

/* Microkit patched variables */
// blk_storage_info_t *blk_driver_storage_info;
// blk_req_queue_t *blk_driver_req_queue;
// blk_resp_queue_t *blk_driver_resp_queue;
// uintptr_t blk_driver_data;
// uintptr_t blk_data_paddr_driver;
// blk_storage_info_t *blk_client_storage_info;
// blk_req_queue_t *blk_client_req_queue;
// blk_resp_queue_t *blk_client_resp_queue;
// uintptr_t blk_client_data;
// uintptr_t blk_client0_data_paddr;
// uintptr_t blk_client1_data_paddr;

/* Driver queue handle */
blk_queue_handle_t drv_h;

/* Client specific info */
typedef struct client {
    blk_queue_handle_t queue_h;
    microkit_channel ch;
    uint32_t start_sector;
    uint32_t sectors;
} client_t;
client_t clients[MAX_NUM_CLIENTS];

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

/* The virtualiser is not initialised until we can read the MBR and populate the block device configuration. */
bool initialised = false;

static void partitions_init()
{
    if (msdos_mbr.signature != MSDOS_MBR_SIGNATURE) {
        LOG_BLK_VIRT_ERR("Invalid MBR signature\n");
        return;
    }

    /* Validate partition and assign to client */
    for (int i = 0; i < config.num_clients; i++) {
        struct config_client *client = &config.clients[i];
        size_t client_partition = client->partition;

        if (msdos_mbr.partitions[client_partition].type == MSDOS_MBR_PARTITION_TYPE_EMPTY) {
            /* Partition does not exist */
            LOG_BLK_VIRT_ERR(
                "Invalid client partition mapping for client %d: partition: %zu, partition does not exist\n", i,
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
        clients[i].start_sector = msdos_mbr.partitions[client_partition].lba_start;
        clients[i].sectors = msdos_mbr.partitions[client_partition].sectors;

        blk_storage_info_t *curr_blk_storage_info = client->storage_info;
        curr_blk_storage_info->sector_size = config.driver.storage_info->sector_size;
        curr_blk_storage_info->capacity = clients[i].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
        curr_blk_storage_info->read_only = false;
        __atomic_store_n(&curr_blk_storage_info->ready, true, __ATOMIC_RELEASE);
    }
}

static void request_mbr()
{
    int err = 0;
    uintptr_t mbr_paddr = config.driver.data_paddr;
    uintptr_t mbr_vaddr = config.driver.data_vaddr;

    uint32_t mbr_req_id = 0;
    err = ialloc_alloc(&ialloc, &mbr_req_id);
    assert(!err);
    reqsbk[mbr_req_id] = (reqbk_t) { 0, 0, mbr_vaddr, 1, 0 };

    /* Virt-to-driver data region needs to be big enough to transfer MBR data */
    assert(config.driver.data_size >= BLK_TRANSFER_SIZE);
    err = blk_enqueue_req(&drv_h, BLK_REQ_READ, mbr_paddr, 0, 1, mbr_req_id);
    assert(!err);

    microkit_deferred_notify(DRIVER_CH);
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

    reqbk_t mbr_bk = reqsbk[drv_resp_id];
    err = ialloc_free(&ialloc, drv_resp_id);
    assert(!err);

    if (drv_status != BLK_RESP_OK) {
        LOG_BLK_VIRT_ERR("Failed to read sector 0 from driver\n");
        return false;
    }

    /* TODO: This is a raw seL4 system call because Microkit does not (currently)
     * include a corresponding libmicrokit API. */
    seL4_ARM_VSpace_Invalidate_Data(3, mbr_bk.vaddr, mbr_bk.vaddr + (BLK_TRANSFER_SIZE * mbr_bk.count));
    sddf_memcpy(&msdos_mbr, (void *)mbr_bk.vaddr, sizeof(struct msdos_mbr));

    return true;
}

void init(void)
{
    config_debug_print(&config);

    while (!blk_storage_is_ready(config.driver.storage_info));

    /* Initialise client queues */
    for (int i = 0; i < config.num_clients; i++) {
        struct config_client *client = &config.clients[i];
        blk_req_queue_t *curr_req = client->req_queue;
        blk_resp_queue_t *curr_resp = client->resp_queue;
        uint32_t queue_capacity = client->queue_capacity;
        blk_queue_init(&clients[i].queue_h, curr_req, curr_resp, queue_capacity);
        clients[i].ch = CLI_CH_OFFSET + i;
    }

    /* Initialise driver queue */
    blk_queue_init(&drv_h, config.driver.req_queue, config.driver.resp_queue, BLK_QUEUE_CAPACITY_DRIV);

    /* Initialise index allocator */
    ialloc_init(&ialloc, ialloc_idxlist, BLK_QUEUE_CAPACITY_DRIV);

    request_mbr();
}

static void handle_driver()
{
    bool client_notify[MAX_NUM_CLIENTS] = { 0 };

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
    for (int i = 0; i < config.num_clients; i++) {
        if (client_notify[i]) {
            microkit_notify(clients[i].ch);
        }
    }
}

static bool handle_client(int cli_id)
{
    int err = 0;
    blk_queue_handle_t h = clients[cli_id].queue_h;
    uintptr_t cli_data_base = config.clients[cli_id].data_paddr;
    uint64_t cli_data_region_size = config.clients[cli_id].data_size;

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

            if ((cli_data_base + cli_offset) % BLK_TRANSFER_SIZE != 0) {
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

        err = blk_enqueue_req(&drv_h, cli_code, cli_data_base + cli_offset, drv_block_number, cli_count,
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
    for (int i = 0; i < config.num_clients; i++) {
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
        bool success = handle_mbr_reply();
        if (success) {
            partitions_init();
            initialised = true;
        };
        return;
    }

    if (ch == DRIVER_CH) {
        handle_driver();
        handle_clients();
    } else {
        handle_clients();
    }
}
