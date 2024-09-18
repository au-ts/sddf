/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/util/fsmalloc.h>
#include <sddf/util/ialloc.h>

#include "blk_config.h"

#define DRIVER_BLK_QUEUE_CH  0
#define DRIVER_BLK_STATE_CH  1
#define CLI_CH_BASE          2

/* Expects channels like [ DRV_BLK_QUEUE, DRV_STATE, CLI0_BLK, CLI0_STATE,
                           CLI1_BLK, CLI1_STATE, ... ] */
#define CLI_CH_BLK_QUEUE_IDX  0
#define CLI_CH_BLK_STATE_IDX  1
#define CLI_CH_STRIDE         2

/* Uncomment this to enable debug logging */
// #define DEBUG_BLK_VIRT

#if defined(DEBUG_BLK_VIRT)
#define LOG_BLK_VIRT(...) do{ sddf_dprintf("BLK_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_BLK_VIRT(...) do{}while(0)
#endif
#define LOG_BLK_VIRT_ERR(...) do{ sddf_dprintf("BLK_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

/*
 * Convert a virtual address within the block data region into a physical
 * address for the driver to give to the device for DMA.
 */
#define BLK_DRIV_TO_PADDR(addr) ((addr) - blk_data_driver + blk_data_driver_paddr)

extern uintptr_t blk_data_driver;
extern uintptr_t blk_data_driver_paddr;

extern blk_storage_info_t *blk_config;
extern blk_storage_info_t *blk_config_driver;

extern blk_queue_handle_t drv_h;
extern fsmalloc_t fsmalloc;
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
 *
 * @return 0 on success, -1 on failure (e.g. out of bounds request)
 */
int get_drv_block_number(uint32_t cli_block_number, uint16_t cli_count, int cli_id, uint32_t *drv_block_number);

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
