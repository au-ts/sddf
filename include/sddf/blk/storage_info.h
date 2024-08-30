/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

#define BLK_STORAGE_INFO_REGION_SIZE 0x1000

/* Device serial number max string length */
#define BLK_MAX_SERIAL_NUMBER 63

typedef struct blk_storage_info {
    char serial_number[BLK_MAX_SERIAL_NUMBER + 1];
    /* device does not accept write requests */
    bool read_only;
    /* whether this configuration is populated yet */
    bool ready;
    /* size of a sector, in bytes */
    uint16_t sector_size;
    /* optimal block size, specified in BLK_TRANSFER_SIZE sized units */
    uint16_t block_size;
    uint16_t queue_depth;
    /* geometry to guide FS layout */
    uint16_t cylinders, heads, blocks;
    /* total capacity of the device, specified in BLK_TRANSFER_SIZE sized units. */
    uint64_t capacity;
} blk_storage_info_t;

/**
 * Load from shared memory whether the block storage device is ready.
 * This does an atomic acquire operation.
 *
 * @param storage_info the block storage device to check
 * @return true the block storage device is ready to use
 * @return false the block storage device is not ready (removed, or initialising)
 */
static inline bool blk_storage_is_ready(blk_storage_info_t *storage_info)
{
    return __atomic_load_n(&storage_info->ready, __ATOMIC_ACQUIRE);
}
