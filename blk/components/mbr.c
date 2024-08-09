#include <microkit.h>
#include <sddf/blk/msdos_mbr.h>
#include <sddf/blk/queue.h>
#include <sddf/util/fsmalloc.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#include "blk_config.h"

/* MS-DOS Master boot record */
struct msdos_mbr msdos_mbr;

typedef struct client {
    uint32_t start_sector;
    uint32_t sectors;
} client_t;
static client_t clients[BLK_NUM_CLIENTS];


#if defined(DEBUG_BLK_VIRT)
#define LOG_BLK_VIRT(...) do{ sddf_dprintf("BLK_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_BLK_VIRT(...) do{}while(0)
#endif
#define LOG_BLK_VIRT_ERR(...) do{ sddf_dprintf("BLK_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

#define BLK_DRIV_TO_PADDR(addr) ((addr) - blk_data_driver + blk_data_driver_paddr)
extern uintptr_t blk_data_driver;
extern uintptr_t blk_data_driver_paddr;

static void partitions_init(blk_storage_info_t *blk_config, blk_storage_info_t *blk_config_driver)
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
        curr_blk_config->read_only = false;
        __atomic_store_n(&curr_blk_config->ready, true, __ATOMIC_RELEASE);
    }
}

static uintptr_t mbr_addr;
static uint64_t mbr_count = 1;

static void request_mbr(fsmalloc_t *fsmalloc, ialloc_t *ialloc, blk_queue_handle_t *drv_h, microkit_channel driver_ch)
{
    int err = fsmalloc_alloc(fsmalloc, &mbr_addr, mbr_count);
    assert(!err);

    uint32_t mbr_req_id = 0; /* uninit */
    err = ialloc_alloc(ialloc, &mbr_req_id);
    assert(!err);

    err = blk_enqueue_req(drv_h, BLK_REQ_READ, BLK_DRIV_TO_PADDR(mbr_addr), 0, mbr_count, mbr_req_id);
    assert(!err);

    microkit_deferred_notify(driver_ch);
}

static bool handle_mbr_reply(fsmalloc_t *fsmalloc, ialloc_t *ialloc, blk_queue_handle_t *drv_h)
{
    int err = 0;

    if (blk_queue_empty_resp(drv_h)) {
        LOG_BLK_VIRT("Notified by driver but queue is empty, expecting a response to READ into sector 0\n");
        return false;
    }

    blk_resp_status_t drv_status;
    uint16_t drv_success_count;
    uint32_t drv_resp_id;
    err = blk_dequeue_resp(drv_h, &drv_status, &drv_success_count, &drv_resp_id);
    assert(!err);

    ialloc_free(ialloc, drv_resp_id);

    if (drv_status != BLK_RESP_OK) {
        LOG_BLK_VIRT_ERR("Failed to read sector 0 from driver\n");
        return false;
    }

    /* TODO: This is a raw seL4 system call because Microkit does not (currently)
     * include a corresponding libmicrokit API. */
    seL4_ARM_VSpace_Invalidate_Data(3, mbr_addr, mbr_addr + (BLK_TRANSFER_SIZE * mbr_count));
    sddf_memcpy(&msdos_mbr, (void *)mbr_addr, sizeof(struct msdos_mbr));
    fsmalloc_free(fsmalloc, mbr_addr, mbr_count);

    return true;
}

bool setup_clients(fsmalloc_t *fsmalloc, ialloc_t *ialloc, blk_queue_handle_t *drv_h, microkit_channel driver_ch, blk_storage_info_t *blk_config, blk_storage_info_t *blk_config_driver)
{
    static bool sent = false;
    if (!sent) {
        sent = true;
        request_mbr(fsmalloc, ialloc, drv_h, driver_ch);
        return false;
    } else {
        bool sent2 = handle_mbr_reply(fsmalloc, ialloc, drv_h);
        if (!sent2) {
            return false;
        }

        partitions_init(blk_config, blk_config_driver);
        return true;
    }
}

int client_get_drv_block_number(int cli_id, uint32_t cli_block_number, blk_req_code_t cli_code, uint16_t cli_count, uint32_t *ret_drv_block_number)
{
    uint32_t drv_block_number = cli_block_number + (clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE));

    if (cli_code == BLK_REQ_READ || cli_code == BLK_REQ_WRITE) {
        // Check if client request is within its allocated bounds
        unsigned long client_sectors = clients[cli_id].sectors / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
        unsigned long client_start_sector = clients[cli_id].start_sector / (BLK_TRANSFER_SIZE / MSDOS_MBR_SECTOR_SIZE);
        if (drv_block_number < client_start_sector || drv_block_number + cli_count > client_start_sector + client_sectors) {
            return -1;
        }
    }

    *ret_drv_block_number = drv_block_number;
    return 0;
}
