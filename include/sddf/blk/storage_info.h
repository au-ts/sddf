/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

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
