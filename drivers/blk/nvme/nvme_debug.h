/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/*
 * Debug-only helpers.
 */

#include <stdint.h>
#include <sddf/util/printf.h>
#include "nvme_queue.h"

/* Debug logging and one-off diagnostics helpers. */
// clang-format off
#define LOG_NVME(...) do { sddf_dprintf("NVME|INFO: "); sddf_dprintf(__VA_ARGS__); } while (0)
// clang-format on

#define NVME_DEBUG_ADMIN_CID_GET_LOG_PAGE 0x0009U
/* 0x100 dwords = 1024 bytes = 16 × 64-byte Error Information log entries. [NVMe-2.1 §5.1.12, Fig. 197; §5.1.12.1.2] */
#define NVME_DEBUG_ERROR_LOG_NUMDL        0x0100U

/* Get Log Page CDW10 fields (LID, NUMDL). [NVMe-2.1 §5.1.12, Fig. 197] */
#define NVME_ADMIN_GET_LOG_PAGE_CDW10_LID_SHIFT   0
#define NVME_ADMIN_GET_LOG_PAGE_CDW10_LID_MASK    NVME_BITS_MASK(0, 7)
#define NVME_ADMIN_GET_LOG_PAGE_CDW10_NUMDL_SHIFT 16
#define NVME_ADMIN_GET_LOG_PAGE_CDW10_NUMDL_MASK  NVME_BITS_MASK(16, 31)

/* Build Get Log Page CDW10. [NVMe-2.1 §5.1.12, Fig. 197] */
static inline uint32_t nvme_build_get_log_page_cdw10(uint16_t numdl, uint8_t lid)
{
    return (((uint32_t)numdl << NVME_ADMIN_GET_LOG_PAGE_CDW10_NUMDL_SHIFT) & NVME_ADMIN_GET_LOG_PAGE_CDW10_NUMDL_MASK)
         | (((uint32_t)lid << NVME_ADMIN_GET_LOG_PAGE_CDW10_LID_SHIFT) & NVME_ADMIN_GET_LOG_PAGE_CDW10_LID_MASK);
}

/* Log Page Identifier values used by this driver. [NVMe-2.1 Fig. 202] */
#define NVME_LOG_PAGE_LID_ERROR_INFO 0x01U /* Error Information */

/* Debug API. */
void nvme_debug_dump_controller_regs(volatile nvme_controller_t *nvme_controller);
nvme_completion_queue_entry_t nvme_queue_submit_and_consume_poll(nvme_queue_info_t *queue,
                                                                 nvme_submission_queue_entry_t *entry);
void nvme_debug_get_error_information_log_page(nvme_queue_info_t *admin_queue, uint64_t data_paddr,
                                               volatile void *data);
