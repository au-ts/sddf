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

/**
 * Load from shared memory whether the block storage device is ready.
 * This does an atomic acquire operation.
 *
 * @attention Due to the asynchronous nature of this system, even if the state
 * has not "changed", the notification about it would have derived from a
 * change...For instance, Ready -> Not Ready -> Ready could be seen as just the
 * sequence Ready -> Ready, but the block device may have changed. Clients
 * should reperform any initialisation necessary.
 *
 * @param storage_info the block storage device to check
 * @return true the block storage device is ready to use
 * @return false the block storage device is not ready (removed, or initialising)
 */
static inline bool blk_storage_is_ready(blk_storage_info_t *storage_info)
{
    return __atomic_load_n(&storage_info->ready, __ATOMIC_ACQUIRE);
}

/**
 * Store in shared memory the block storage device ready state, and notify on
 * the Block State notification channel that we had a state change.
 *
 * @param storage_info
 * @param ch
 * @param ready
 */
static inline void blk_storage_notify_ready(blk_storage_info_t *storage_info, microkit_channel ch, bool ready)
{
    __atomic_store_n(&storage_info->ready, ready, __ATOMIC_RELEASE);

    /* Correctness: We always want to notify on a state change, even if it
       appears to be a noop, because if we had IRQs showing In -> Out -> In,
       we might only see the In->In states.
    */
    microkit_notify(ch);
}
