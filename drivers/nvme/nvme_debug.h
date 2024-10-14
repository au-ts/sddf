#pragma once

#include <stdint.h>
#include "nvme.h"
#include "nvme_queue.h"
#include <sddf/util/printf.h>

// clang-format off
#define LOG_NVME(...) do{ sddf_dprintf("NVME|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
// clang-format on

static void nvme_debug_dump_controller_regs(volatile nvme_controller_t *nvme_controller)
{
    LOG_NVME("CAP: %016lx\n", nvme_controller->cap);
    LOG_NVME("VS: major: %u, minor: %u, tertiary: %u\n", nvme_controller->vs.mjr, nvme_controller->vs.mnr,
             nvme_controller->vs.ter);
    LOG_NVME("INTMS: %08x\n", nvme_controller->intms);
    LOG_NVME("INTMC: %08x\n", nvme_controller->intmc);
    LOG_NVME("CC: %08x\n", nvme_controller->cc);
    LOG_NVME("CSTS: %08x\n", nvme_controller->csts);
    LOG_NVME("AQA: %08x\n", nvme_controller->aqa);
    LOG_NVME("ASQ: %016lx\n", nvme_controller->asq);
    LOG_NVME("ACQ: %016lx\n", nvme_controller->acq);
}

static nvme_completion_queue_entry_t nvme_queue_submit_and_consume_poll(nvme_queue_info_t *queue,
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
    }
}

// TODO: tidy up.
/* 5.1.12.1.2  Error Information (Log Page Identifier 01h) */
typedef struct {
    uint64_t ecnt; /* Error Count; unique ID for this error. (retained across power off) */
    uint16_t sqid; /* Submission Queue ID */
    uint16_t cid;  /* Command ID */
    uint16_t sts;  /* Status Info (from the completion queue entry - Status + Phase) */
    uint16_t pel;  /* Parameter Error location (!!!!) */
    uint64_t lba;  /* Logical Block Address */
    uint32_t nsid;
    uint8_t vsia; /* vendor specific info available */
    uint8_t trtype; /* transport type */
    uint8_t csi; /* command set indiciator (valid if version > 0x1)*/
    uint8_t opc; /* opcode (valid if version > 0x1)*/
    uint64_t csinfo; /* command specific information (if specified in the command) */
    uint16_t ttsi; /* transport type specification information */
    uint8_t _reserved[20];
    uint8_t lpver; /* log page version */
} nvme_error_information_log_page_t;
_Static_assert(sizeof(nvme_error_information_log_page_t) == 64, "should be 64 bytes.");

static void nvme_debug_get_error_information_log_page(nvme_queue_info_t *admin_queue, uint64_t data_paddr,
                                                      volatile void *data)
{
    LOG_NVME("!!! LOG PAGE !!!\n");
    nvme_completion_queue_entry_t entry;
    entry = nvme_queue_submit_and_consume_poll(
        admin_queue, &(nvme_submission_queue_entry_t) {
                         .cdw0 = /* CID */ (0b1001 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x2,
                         .prp2 = 0,
                         .prp1 = data_paddr,
                         .cdw10 = /* NUMDL*/ (0x100 << 16) | /* LID*/ 0x01,
                         .cdw11 = 0x0,
                         .cdw12 = 0x0,
                     });

    assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

    volatile nvme_error_information_log_page_t *errors = data;
    for (int i = 0; i < 2; i++) {
        LOG_NVME("Error 0x%lx\n", errors[i].ecnt);
        // These produce Store/AMO faults, NEAR THE BEGINNING of this function??? TODO???
        LOG_NVME("\tSQID: 0x%x\n", errors[i].sqid);
        LOG_NVME("\t CID: 0x%x\n", errors[i].cid);
        LOG_NVME("\t STS: 0x%x\n", errors[i].sts);
        LOG_NVME("\t PEL: 0x%x\n", errors[i].pel);
        LOG_NVME("\t(elided)\n");
    }
}
