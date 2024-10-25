/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <sddf/blk/config.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>

#define DRIVER_MAX_NUM_BUFFERS 1024

extern blk_virt_config_t config;

/* Uncomment this to enable debug logging */
// #define DEBUG_BLK_VIRT

#if defined(DEBUG_BLK_VIRT)
#define LOG_BLK_VIRT(...) do{ sddf_dprintf("BLK_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_BLK_VIRT(...) do{}while(0)
#endif
#define LOG_BLK_VIRT_ERR(...) do{ sddf_dprintf("BLK_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

extern blk_queue_handle_t drv_h;
extern ialloc_t ialloc;

// These functions are called by the virtualiser for handling the policy parts of
// virtualising access to the driver.

/**
 * Get the block number for the driver from the client's request information.
 *
 * @param cli_block_number the block number the client requested
 * @param cli_count the number of blocks the client requested
 * @param cli_id the client ID number
 * @param drv_block_number the address of variable to store the block number in
 */
blk_resp_status_t get_drv_block_number(uint64_t cli_block_number, uint16_t cli_count, int cli_id,
                                       uint64_t *drv_block_number);

/**
 * Initialise the policy component
 *
 * @return true when ready
 */
bool policy_init(void);

/**
 * Reset the policy components' state.
 */
void policy_reset(void);
