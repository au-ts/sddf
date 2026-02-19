/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <sddf/util/util.h>
#include "nvme_debug.h"

void nvme_debug_dump_controller_regs(volatile nvme_controller_t *nvme_controller)
{
    LOG_NVME("CAP: %016lx\n", nvme_controller->cap);
    uint32_t vs = nvme_controller->vs;
    LOG_NVME("VS: major: %lu, minor: %lu, tertiary: %lu\n", (vs & NVME_VS_MJR_MASK) >> NVME_VS_MJR_SHIFT,
             (vs & NVME_VS_MNR_MASK) >> NVME_VS_MNR_SHIFT, (vs & NVME_VS_TER_MASK) >> NVME_VS_TER_SHIFT);
    LOG_NVME("INTMS: %08x\n", nvme_controller->intms);
    LOG_NVME("INTMC: %08x\n", nvme_controller->intmc);
    LOG_NVME("CC: %08x\n", nvme_controller->cc);
    LOG_NVME("CSTS: %08x\n", nvme_controller->csts);
    LOG_NVME("AQA: %08x\n", nvme_controller->aqa);
    LOG_NVME("ASQ: %016lx\n", nvme_controller->asq);
    LOG_NVME("ACQ: %016lx\n", nvme_controller->acq);
}

nvme_completion_queue_entry_t nvme_queue_submit_and_consume_poll(nvme_queue_info_t *queue,
                                                                 nvme_submission_queue_entry_t *entry)
{
    nvme_queue_submit(queue, entry);

    nvme_completion_queue_entry_t response;
    int i = 0;
    while (true) {
        int ret = nvme_queue_consume(queue, &response);
        if (ret == 0) {
            LOG_NVME("received a response for submission with CDW0: %x\n", entry->cdw0);
            return response;
        }

        if (i % 100 == 0) {
            LOG_NVME("waiting for response to submission with CDW0: %x\n", entry->cdw0);
        }
        i++;
    }
}

/* Error Information (Log Page Identifier 01h). [NVMe-2.1 §5.1.12.1.2, Fig. 205] */
typedef struct {
    uint64_t ecnt;   /* Error Count; unique ID for this error. (retained across power off) */
    uint16_t sqid;   /* Submission Queue ID */
    uint16_t cid;    /* Command ID */
    uint16_t sts;    /* Status Info (from the completion queue entry - Status + Phase) */
    uint16_t pel;    /* Parameter Error Location (byte + bit in failing field). */
    uint64_t lba;    /* Logical Block Address */
    uint32_t nsid;   /* Namespace Identifier */
    uint8_t vsia;    /* vendor specific info available */
    uint8_t trtype;  /* transport type */
    uint8_t csi;     /* command set indiciator (valid if version > 0x1)*/
    uint8_t opc;     /* opcode (valid if version > 0x1)*/
    uint64_t csinfo; /* command specific information (if specified in the command) */
    uint16_t ttsi;   /* transport type specification information */
    uint8_t _reserved[20];
    uint8_t lpver;   /* log page version */
} nvme_error_information_log_page_t;
_Static_assert(sizeof(nvme_error_information_log_page_t) == 64, "should be 64 bytes.");

void nvme_debug_get_error_information_log_page(nvme_queue_info_t *admin_queue, uint64_t data_paddr, volatile void *data)
{
    LOG_NVME("!!! LOG PAGE !!!\n");
    nvme_completion_queue_entry_t entry;
    entry = nvme_queue_submit_and_consume_poll(
        admin_queue,
        &(nvme_submission_queue_entry_t) {
            .cdw0 = nvme_build_cdw0(NVME_DEBUG_ADMIN_CID_GET_LOG_PAGE, NVME_ADMIN_OP_GET_LOG_PAGE, NVME_CDW0_PSDT_PRP),
            .dptr2 = 0,
            .dptr1 = data_paddr,
            .cdw10 = nvme_build_get_log_page_cdw10(NVME_DEBUG_ERROR_LOG_NUMDL, NVME_LOG_PAGE_LID_ERROR_INFO),
            .cdw11 = 0,
            .cdw12 = 0,
        });

    /* Status field semantics for successful completion. [NVMe-2.1 §4.2.3] */
    assert((entry.phase_tag_and_status & NVME_CQE_STATUS_MASK) >> NVME_CQE_STATUS_SHIFT == 0);

    volatile nvme_error_information_log_page_t *errors = data;
    for (int i = 0; i < 2; i++) {
        LOG_NVME("Error 0x%lx\n", errors[i].ecnt);
        LOG_NVME("\tSQID: 0x%x\n", errors[i].sqid);
        LOG_NVME("\t CID: 0x%x\n", errors[i].cid);
        LOG_NVME("\t STS: 0x%x\n", errors[i].sts);
        LOG_NVME("\t PEL: 0x%x\n", errors[i].pel);
        LOG_NVME("\t(elided)\n");
    }
}
