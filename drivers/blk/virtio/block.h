/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/util/printf.h>

// #define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("BLK DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("BLK DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

/*
 * This is specific to our driver, and not the virtIO specification.
 * We split our requests to avoid copying and so we do not put the
 * whole header in the first descriptor of a request which is why
 * this is smaller than the size of virtio_blk_req
 */
#define VIRTIO_BLK_REQ_HDR_SIZE 16

/* This driver does not support legacy mode */
#define VIRTIO_BLK_DRIVER_VERSION 2

#define VIRTIO_BLK_SECTOR_SIZE 512

#define VIRTIO_BLK_T_IN            0
#define VIRTIO_BLK_T_OUT           1
#define VIRTIO_BLK_T_FLUSH         4
#define VIRTIO_BLK_T_GET_ID        8
#define VIRTIO_BLK_T_GET_LIFETIME 10
#define VIRTIO_BLK_T_DISCARD      11
#define VIRTIO_BLK_T_WRITE_ZEROES 13
#define VIRTIO_BLK_T_SECURE_ERASE 14

#define VIRTIO_BLK_S_OK 0
#define VIRTIO_BLK_S_IOERR 1
#define VIRTIO_BLK_S_UNSUPP 2

#define VIRTIO_BLK_F_SIZE_MAX        1  /* Indicates maximum segment size */
#define VIRTIO_BLK_F_SEG_MAX         2  /* Indicates maximum # of segments */
#define VIRTIO_BLK_F_GEOMETRY        4  /* Legacy geometry available  */
#define VIRTIO_BLK_F_RO              5  /* Disk is read-only */
#define VIRTIO_BLK_F_BLK_SIZE        6  /* Block size of disk is available*/
#define VIRTIO_BLK_F_TOPOLOGY       10  /* Topology information is available */
#define VIRTIO_BLK_F_MQ             12  /* support more than one vq */
#define VIRTIO_BLK_F_DISCARD        13  /* DISCARD is supported */
#define VIRTIO_BLK_F_WRITE_ZEROES   14  /* WRITE ZEROES is supported */
#define VIRTIO_BLK_F_SECURE_ERASE   16  /* Secure Erase is supported */
#define VIRTIO_BLK_F_ZONED          17  /* Zoned block device */

struct virtio_blk_config {
    uint64_t capacity;
    uint32_t size_max;
    uint32_t seg_max;
    struct virtio_blk_geometry {
        uint16_t cylinders;
        uint8_t heads;
        uint8_t sectors;
    } geometry;
    uint32_t blk_size;
    struct virtio_blk_topology {
        // # of logical blocks per physical block (log2)
        uint8_t physical_block_exp;
        // offset of first aligned logical block
        uint8_t alignment_offset;
        // suggested minimum I/O size in blocks
        uint16_t min_io_size;
        // optimal (suggested maximum) I/O size in blocks
        uint32_t opt_io_size;
    } topology;
    uint8_t writeback;
    uint8_t unused0;
    uint16_t num_queues;
    uint32_t max_discard_sectors;
    uint32_t max_discard_seg;
    uint32_t discard_sector_alignment;
    uint32_t max_write_zeroes_sectors;
    uint32_t max_write_zeroes_seg;
    uint8_t write_zeroes_may_unmap;
    uint8_t unused1[3];
    uint32_t max_secure_erase_sectors;
    uint32_t max_secure_erase_seg;
    uint32_t secure_erase_sector_alignment;
};

struct virtio_blk_req {
    uint32_t type;
    uint32_t reserved;
    uint64_t sector;
    /* Here there would also be uint8_t data[], but in our case
     * we put the data in a separate descriptors */
    uint8_t status;
};

static void virtio_blk_print_req(struct virtio_blk_req *req)
{
    LOG_DRIVER("type: 0x%x, reserved: 0x%x, sector: 0x%lx, status: 0x%x\n",
               req->type, req->reserved, req->sector, req->status);
}

static void virtio_blk_print_config(volatile struct virtio_blk_config *config)
{
    LOG_DRIVER("capacity: 0x%lx (0x%lx bytes)\n", config->capacity, config->capacity * VIRTIO_BLK_SECTOR_SIZE);
    LOG_DRIVER("size_max: 0x%x\n", config->size_max);
    LOG_DRIVER("seg_max: 0x%x\n", config->seg_max);
    LOG_DRIVER("geometry.cylinders: 0x%x\n", config->geometry.cylinders);
    LOG_DRIVER("geometry.heads: 0x%x\n", config->geometry.heads);
    LOG_DRIVER("geometry.sectors: 0x%x\n", config->geometry.sectors);
    LOG_DRIVER("blk_size: 0x%x\n", config->blk_size);
    LOG_DRIVER("topology.physical_block_exp: 0x%hhx\n", config->topology.physical_block_exp);
    LOG_DRIVER("topology.alignment_offset: 0x%hhx\n", config->topology.alignment_offset);
    LOG_DRIVER("topology.min_io_size: 0x%hx\n", config->topology.min_io_size);
    LOG_DRIVER("topology.opt_io_size: 0x%x\n", config->topology.opt_io_size);
    LOG_DRIVER("writeback: 0x%hhx\n", config->writeback);
    LOG_DRIVER("num_queues: 0x%hx\n", config->num_queues);
    LOG_DRIVER("max_discard_sectors: 0x%x\n", config->max_discard_sectors);
    LOG_DRIVER("max_discard_seg: 0x%x\n", config->max_discard_seg);
    LOG_DRIVER("discard_sector_alignment: 0x%x\n", config->discard_sector_alignment);
    LOG_DRIVER("max_write_zeroes_sectors: 0x%x\n", config->max_write_zeroes_sectors);
    LOG_DRIVER("max_write_zeroes_seg: 0x%x\n", config->max_write_zeroes_seg);
    LOG_DRIVER("write_zeroes_may_unmap: 0x%hhx\n", config->write_zeroes_may_unmap);
    LOG_DRIVER("max_secure_erase_sectors: 0x%x\n", config->max_secure_erase_sectors);
    LOG_DRIVER("max_secure_erase_seg: 0x%x\n", config->max_secure_erase_seg);
    LOG_DRIVER("secure_erase_sector_alignment: 0x%x\n", config->secure_erase_sector_alignment);
}

static void virtio_blk_print_features(uint64_t features)
{
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_SIZE_MAX)) {
        LOG_DRIVER("    VIRTIO_BLK_F_SIZE_MAX\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_SEG_MAX)) {
        LOG_DRIVER("    VIRTIO_BLK_F_SEG_MAX\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_GEOMETRY)) {
        LOG_DRIVER("    VIRTIO_BLK_F_GEOMETRY\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_RO)) {
        LOG_DRIVER("    VIRTIO_BLK_F_RO\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_BLK_SIZE)) {
        LOG_DRIVER("    VIRTIO_BLK_F_BLK_SIZE\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_TOPOLOGY)) {
        LOG_DRIVER("    VIRTIO_BLK_F_TOPOLOGY\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_MQ)) {
        LOG_DRIVER("    VIRTIO_BLK_F_MQ\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_DISCARD)) {
        LOG_DRIVER("    VIRTIO_BLK_F_DISCARD\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_WRITE_ZEROES)) {
        LOG_DRIVER("    VIRTIO_BLK_F_WRITE_ZEROES\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_SECURE_ERASE)) {
        LOG_DRIVER("    VIRTIO_BLK_F_SECURE_ERASE\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_BLK_F_ZONED)) {
        LOG_DRIVER("    VIRTIO_BLK_F_ZONED\n");
    }
    virtio_print_reserved_feature_bits(features);
}
