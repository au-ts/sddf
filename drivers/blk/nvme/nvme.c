/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/config.h>
#include <sddf/blk/storage_info.h>
#include <sddf/util/util.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <sddf/timer/config.h>
#include <sddf/timer/client.h>

#include "nvme.h"
#include "nvme_queue.h"

#define DEBUG_DRIVER
#ifdef DEBUG_DRIVER
#include "nvme_debug.h"
#define UNUSED
#else
#define LOG_NVME(...)
#define UNUSED __attribute__((unused))
#endif

#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "code assumes little endian CPU as NVMe/PCIe is little endian"
#endif

volatile nvme_controller_t *nvme_controller;
nvme_submission_queue_entry_t *nvme_asq_region;
nvme_completion_queue_entry_t *nvme_acq_region;
uintptr_t nvme_asq_region_paddr;
uintptr_t nvme_acq_region_paddr;
nvme_submission_queue_entry_t *nvme_io_sq_region;
nvme_completion_queue_entry_t *nvme_io_cq_region;
uintptr_t nvme_io_sq_region_paddr;
uintptr_t nvme_io_cq_region_paddr;

nvme_identify_ctrl_t *nvme_identify_ctrl;
nvme_identify_ns_t *nvme_identify_ns;

/* Timed polling used while waiting for controller reset/enable transitions. */
#define NVME_CONTROLLER_STATUS_POLL_INTERVAL_MS 10
#define NVME_CONTROLLER_STATUS_POLL_INTERVAL_NS (NVME_CONTROLLER_STATUS_POLL_INTERVAL_MS * NS_IN_MS)

/* Admin queue has ID 0 [NVMe-2.1 §1.5.4]; I/O queues use IDs 1-65535. [NVMe-2.1 §3.3.3.2] */
/* Only one I/O queue pair is supported and share ID 1. */
#define NVME_DEFAULT_IO_Q_ID 1
/* One IV corresponds to one I/O queue pair. [NVMe-2.1 §5.2.1, Fig. 475] */
#define NVME_CREATE_IO_Q_INTERRUPT_VECTOR 0

/* Valid NSIDs are 1h through FFFFFFFFh. [NVMe-2.1 §3.2.1.1] */
/* Only a single namespace is supported. */
#define NVME_DEFAULT_NSID 1

static nvme_queue_info_t admin_queue;
static nvme_queue_info_t io_queue;

static blk_queue_handle_t blk_queue;
static blk_storage_info_t *storage_info;

/*
 * State machine flow:
 *   WAIT_NOT_READY -> WAIT_READY -> WAIT_IDENTIFY_CTRL (timer-driven, see nvme_poll_controller_status)
 *   WAIT_IDENTIFY_CTRL -> WAIT_IDENTIFY_NS -> WAIT_CREATE_IO_CQ -> WAIT_CREATE_IO_SQ -> READY (IRQ-driven, see handle_admin_completions)
 */
typedef enum {
    NVME_STATE_WAIT_NOT_READY,    // Waiting for CSTS.RDY=0
    NVME_STATE_WAIT_READY,        // Waiting for CSTS.RDY=1
    NVME_STATE_WAIT_IDENTIFY_CTRL,// Waiting for Identify Controller completion
    NVME_STATE_WAIT_IDENTIFY_NS,  // Waiting for Identify Namespace completion
    NVME_STATE_WAIT_CREATE_IO_CQ, // Waiting for Create I/O CQ completion
    NVME_STATE_WAIT_CREATE_IO_SQ, // Waiting for Create I/O SQ completion
    NVME_STATE_READY,             // Operational
} nvme_state_t;

typedef struct {
    nvme_state_t state;
    uint32_t timeout_ms;        // CAP.TO derived timeout
    uint32_t waited_ms;         // Time waited in current state
    uint32_t io_queue_depth;    // Configured I/O queue depth based on CAP.MQES
    uint32_t sectors_per_block; // Derived from Identify Namespace data
} nvme_state_ctx_t;

static nvme_state_ctx_t state_ctx;

#define fallthrough __attribute__((__fallthrough__))

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".blk_driver_config"))) blk_driver_config_t blk_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

/* Admin queue max 4096 entries, I/O queue max 65536 entries. [NVMe-2.1 §3.3.3.1] */
#define NVME_ASQ_CAPACITY (NVME_ASQ_REGION_SIZE / sizeof(nvme_submission_queue_entry_t))
#define NVME_ACQ_CAPACITY (NVME_ACQ_REGION_SIZE / sizeof(nvme_completion_queue_entry_t))
_Static_assert(NVME_ASQ_CAPACITY <= 0x1000, "capacity of ASQ must be <=4096 (entries)");
_Static_assert(NVME_ACQ_CAPACITY <= 0x1000, "capacity of ACQ must be <=4096 (entries)");
#define NVME_IO_SQ_CAPACITY (NVME_IO_SQ_REGION_SIZE / sizeof(nvme_submission_queue_entry_t))
#define NVME_IO_CQ_CAPACITY (NVME_IO_CQ_REGION_SIZE / sizeof(nvme_completion_queue_entry_t))
_Static_assert(NVME_IO_SQ_CAPACITY <= 0x10000, "capacity of IO SQ must be <=65536 (entries)");
_Static_assert(NVME_IO_CQ_CAPACITY <= 0x10000, "capacity of IO CQ must be <=65536 (entries)");

/* Map sDDF IDs to NVMe CIDs - align with I/O queue depth */
#define MAX_PENDING_REQS NVME_IO_SQ_CAPACITY

/* PRP List Configuration */
#define MAX_TRANSFER_PAGES 32   /* 128KB max transfer (32 * 4KB pages) */
#define PRP_LIST_SLOT_SIZE 256
#define PRP_LIST_REGION_SIZE (MAX_PENDING_REQS * PRP_LIST_SLOT_SIZE)
#define NVME_PRP_ENTRIES_PER_PAGE       ((uint32_t)(PRP_LIST_SLOT_SIZE / sizeof(uint64_t)))
#define NVME_PRP_NON_CHAINED_MAX_PAGES  (1 + NVME_PRP_ENTRIES_PER_PAGE) // PRP1 + List slot

_Static_assert(PRP_LIST_REGION_SIZE <= NVME_PRP_LIST_REGION_SIZE,
               "PRP list region exceeds configured nvme_prp_list region size");

static ialloc_t cid_ialloc;
static uint32_t cid_ialloc_idxlist[MAX_PENDING_REQS];
static uint32_t cid_to_id[MAX_PENDING_REQS];
static uint16_t cid_to_count[MAX_PENDING_REQS];

/*
 * Host queue entry-size exponents for CC.IOSQES/CC.IOCQES.
 * CC stores n where entry size is 2^n; Identify SQES/CQES report valid ranges.
 * [NVMe-2.1 §3.1.4.5; §5.1.13.2.1, Fig. 312]
 */
#define NVME_HOST_IOSQES_EXP ((uint8_t)__builtin_ctz((unsigned int)sizeof(nvme_submission_queue_entry_t)))
#define NVME_HOST_IOCQES_EXP ((uint8_t)__builtin_ctz((unsigned int)sizeof(nvme_completion_queue_entry_t)))
_Static_assert(NVME_HOST_IOSQES_EXP == 6, "Common SQE layout requires 64-byte entries (2^6)");
_Static_assert(NVME_HOST_IOCQES_EXP == 4, "Common CQE layout requires 16-byte entries (2^4)");

/* [NVMe-2.1 §3.1.4.3] */
void nvme_irq_mask(void)
{
    /* [NVMe-PCIe-1.1] 3.5.1.1 Differences between Pin Based and MSI Interrupts
        > Pin-based and single MSI only use one interrupt vector.
        > Multiple MSI may use up to 32 interrupt vectors.

       [NVme-2.1] 3.1.4.10 Admin Completion Queue Base Address
        > This queue is always associated with interrupt vector 0.
    */

    /* For now -- we mask out every interrupt vector) */
    nvme_controller->intms = 0xffffffff;
}

/* [NVMe-2.1 §3.1.4.4] */
void nvme_irq_unmask(void)
{
    /* [NVMe-PCIe-1.1] 3.5.1.1 Differences between Pin Based and MSI Interrupts
        > Pin-based and single MSI only use one interrupt vector.
        > Multiple MSI may use up to 32 interrupt vectors.

       [NVme-2.1] 3.1.4.10 Admin Completion Queue Base Address
        > This queue is always associated with interrupt vector 0.
    */

    /* For now -- we mask in only vector 0, as it's the only one */
    nvme_controller->intmc = 0x1;
}

/* Ensure host SQE/CQE entry sizes fall within controller-advertised limits. */
static void validate_identify_entry_size_limits(void)
{
    /* SQES/CQES bytes encode min/max 2^n entry-size bounds. [NVMe-2.1 Fig. 312] */
    uint8_t minsqes = (nvme_identify_ctrl->sqes & NVME_IDENTIFY_ENTRY_SIZE_MIN_MASK)
                   >> NVME_IDENTIFY_ENTRY_SIZE_MIN_SHIFT;
    uint8_t maxsqes = (nvme_identify_ctrl->sqes & NVME_IDENTIFY_ENTRY_SIZE_MAX_MASK)
                   >> NVME_IDENTIFY_ENTRY_SIZE_MAX_SHIFT;
    uint8_t mincqes = (nvme_identify_ctrl->cqes & NVME_IDENTIFY_ENTRY_SIZE_MIN_MASK)
                   >> NVME_IDENTIFY_ENTRY_SIZE_MIN_SHIFT;
    uint8_t maxcqes = (nvme_identify_ctrl->cqes & NVME_IDENTIFY_ENTRY_SIZE_MAX_MASK)
                   >> NVME_IDENTIFY_ENTRY_SIZE_MAX_SHIFT;

    if (minsqes > maxsqes) {
        sddf_dprintf("NVMe SQES invalid: min %u > max %u\n", minsqes, maxsqes);
        assert(false);
    }

    if (mincqes > maxcqes) {
        sddf_dprintf("NVMe CQES invalid: min %u > max %u\n", mincqes, maxcqes);
        assert(false);
    }

    if (NVME_HOST_IOSQES_EXP < minsqes || NVME_HOST_IOSQES_EXP > maxsqes) {
        sddf_dprintf("NVMe SQES mismatch: controller range [%u, %u], host IOSQES=%u\n", minsqes, maxsqes,
                     NVME_HOST_IOSQES_EXP);
        assert(false);
    }

    if (NVME_HOST_IOCQES_EXP < mincqes || NVME_HOST_IOCQES_EXP > maxcqes) {
        sddf_dprintf("NVMe CQES mismatch: controller range [%u, %u], host IOCQES=%u\n", mincqes, maxcqes,
                     NVME_HOST_IOCQES_EXP);
        assert(false);
    }
}

/* Resolve namespace logical-sector size from active FLBAS/LBAF selection. */
static uint32_t nvme_namespace_sector_size(const nvme_identify_ns_t *identify_ns)
{
    uint8_t format_index = nvme_identify_flbas_format_index(identify_ns->flbas);
    uint8_t lbads = identify_ns->lbaf[format_index].lbads;

    /* Logical block data size (sector size) = 2^LBADS bytes. */
    assert(lbads >= 9);
    return 1 << lbads;
}

/* Copy fixed-width ASCII fields and trim trailing space padding in place. */
static void copy_trim_ascii(char *dst, size_t dst_size, const char *src, size_t src_size)
{
    assert(dst_size >= (src_size + 1));

    memcpy(dst, src, src_size);
    dst[src_size] = '\0';

    while (src_size > 0 && dst[src_size - 1] == ' ') {
        dst[src_size - 1] = '\0';
        src_size--;
    }
}

/* Build PRP pointers for a request using a single non-chained PRP list model. */
static int build_prp_dptr(uint32_t cid, uintptr_t data_paddr, uint16_t count, uint64_t *dptr1, uint64_t *dptr2)
{
    /* Driver currently supports a single PRP-list page only (no chained PRP-list traversal). */
    if (count > NVME_PRP_NON_CHAINED_MAX_PAGES) {
        sddf_dprintf("NVMe: PRP transfer too large for non-chained list (%u pages, max %u)\n", count,
                     NVME_PRP_NON_CHAINED_MAX_PAGES);
        return -1;
    }

    /*
     * PRP handling:
     * - PRP1 = first 4KB page
     * - PRP2 = second 4KB page (for 8KB transfer) or PRP list pointer (for >8KB)
     */
    *dptr1 = data_paddr;
    *dptr2 = 0;

    if (count == 2) {
        /* Simple case: 2 pages. PRP2 points directly to 2nd page. */
        *dptr2 = data_paddr + BLK_TRANSFER_SIZE;
    } else if (count > 2) {
        /* PRP2 points to a PRP List stored in the metadata region. */
        /* x86 hardcoded addresses */
        /* Each CID gets its own PRP list slot in the PRP region */
        uint64_t *prp_list = (uint64_t *)(NVME_PRP_LIST_VADDR + (uint64_t)cid * PRP_LIST_SLOT_SIZE);
        uint64_t prp_list_paddr = NVME_PRP_LIST_PADDR + (uint64_t)cid * PRP_LIST_SLOT_SIZE;

        /* Fill the PRP List */
        for (uint16_t i = 1; i < count; i++) {
            prp_list[i - 1] = data_paddr + ((uint64_t)i * BLK_TRANSFER_SIZE);
        }

        *dptr2 = prp_list_paddr;
    }

    return 0;
}

static void handle_request(void)
{
    bool notify_virt = false;

    blk_req_code_t code;
    uintptr_t req_paddr;
    uint64_t block_number;
    uint16_t count;
    uint32_t id;

    while (true) {
        if (ialloc_num_free(&cid_ialloc) == 0U) {
            LOG_NVME("No free CIDs, deferring request dequeue until completions free slots\n");
            break;
        }

        int err = blk_dequeue_req(&blk_queue, &code, &req_paddr, &block_number, &count, &id);
        if (err != 0) {
            break;
        }

        uint8_t opcode = 0;

        if (code == BLK_REQ_READ) {
            opcode = NVME_OP_READ;
        } else if (code == BLK_REQ_WRITE) {
            opcode = NVME_OP_WRITE;
        } else if (code == BLK_REQ_BARRIER) {
            err = blk_enqueue_resp(&blk_queue, BLK_RESP_OK, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        } else {
            err = blk_enqueue_resp(&blk_queue, BLK_RESP_ERR_INVALID_PARAM, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        }

        if (count == 0) {
            sddf_dprintf("NVMe: rejecting zero-length request\n");
            err = blk_enqueue_resp(&blk_queue, BLK_RESP_ERR_INVALID_PARAM, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        }

        /* Reject oversized transfers */
        if (count > MAX_TRANSFER_PAGES) {
            sddf_dprintf("NVMe: request too large (%u pages, max %u)\n", count, MAX_TRANSFER_PAGES);
            err = blk_enqueue_resp(&blk_queue, BLK_RESP_ERR_UNSPEC, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        }

        /* Translate sDDF 4096B blocks to NVMe device sectors. */
        uint64_t lba = block_number * state_ctx.sectors_per_block;
        uint32_t nlb = (count * state_ctx.sectors_per_block) - 1;

        /* Allocate a CID */
        uint32_t cid;
        err = ialloc_alloc(&cid_ialloc, &cid);
        assert(err == 0);
        cid_to_id[cid] = id;
        cid_to_count[cid] = count;

        uint64_t dptr1 = 0;
        uint64_t dptr2 = 0;
        err = build_prp_dptr(cid, req_paddr, count, &dptr1, &dptr2);
        if (err != 0) {
            err = ialloc_free(&cid_ialloc, cid);
            assert(!err);
            err = blk_enqueue_resp(&blk_queue, BLK_RESP_ERR_UNSPEC, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        }

        nvme_queue_submit(&io_queue, &(nvme_submission_queue_entry_t) {
                                         .cdw0 = nvme_build_cdw0((uint16_t)cid, opcode, NVME_CDW0_PSDT_PRP),
                                         .nsid = NVME_DEFAULT_NSID,
                                         .cdw10 = (uint32_t)lba,
                                         .cdw11 = (uint32_t)(lba >> 32),
                                         .cdw12 = nvme_build_rw_cdw12((uint16_t)nlb, true),
                                         .prp1 = dptr1,
                                         .prp2 = dptr2,
                                     });
    }

    if (notify_virt) {
        sddf_notify(blk_config.virt.id);
    }
}

static void handle_admin_completions(void)
{
    nvme_completion_queue_entry_t entry;

    if (nvme_queue_consume(&admin_queue, &entry) != 0) {
        LOG_NVME("handle_admin_completion: no completion available\n");
        return;
    }

    if (entry.cid >= state_ctx.io_queue_depth || !ialloc_in_use(&cid_ialloc, entry.cid)) {
        sddf_dprintf("NVMe: admin completion with invalid CID=%u dropped\n", entry.cid);
        return;
    }

    int err = ialloc_free(&cid_ialloc, entry.cid);
    assert(err == 0);

    uint16_t status = (entry.phase_tag_and_status & NVME_CQE_STATUS_MASK) >> NVME_CQE_STATUS_SHIFT;
    if (status != 0) {
        sddf_dprintf("NVMe admin command failed with status 0x%x in state %d\n", status, state_ctx.state);
        return;
    }

    LOG_NVME("Admin completion in state %d\n", state_ctx.state);

    switch (state_ctx.state) {
    case NVME_STATE_WAIT_IDENTIFY_CTRL: {
        LOG_NVME("Identify Controller completed\n");
        LOG_NVME("  VID: 0x%04x  SSVID: 0x%04x\n", nvme_identify_ctrl->vid, nvme_identify_ctrl->ssvid);
        LOG_NVME("  SN:  %.20s\n", nvme_identify_ctrl->sn);
        LOG_NVME("  MN:  %.40s\n", nvme_identify_ctrl->mn);
        LOG_NVME("  FR:  %.8s\n", nvme_identify_ctrl->fr);

        // 8. The host determines any I/O Command Set specific configuration information
        //    For now, we assume that the controller supports only the NVM Command Set.

        // 9. Determine the number of I/O Submission Queues and I/O Completion Queues
        //    supported using the Set Features command with the Number of Queues feature identifier.
        //    After determining the number of I/O Queues, the NVMe Transport specific interrupt registers
        //    (e.g., MSI and/or MSI-X registers) should be configured
        validate_identify_entry_size_limits();

        uint32_t admin_cid;
        err = ialloc_alloc(&cid_ialloc, &admin_cid);
        assert(err == 0);
        assert(admin_cid <= UINT16_MAX);

        /*
         * Identify Namespace for the NVM Command Set (CNS=00h).
         * [NVM-CommandSet-1.1 §4.1.5.1, Fig. 114]
         * [NVM-CommandSet-1.1 §4.1.5.1, Fig. 114]
         */
        nvme_queue_submit(&admin_queue,
                          &(nvme_submission_queue_entry_t) {
                              .cdw0 = nvme_build_cdw0((uint16_t)admin_cid, NVME_ADMIN_OP_IDENTIFY, NVME_CDW0_PSDT_PRP),
                              .nsid = NVME_DEFAULT_NSID,
                              .cdw10 = NVME_IDENTIFY_CNS_NAMESPACE,
                              .prp1 = NVME_IDENTIFY_NS_PADDR,
                          });

        state_ctx.state = NVME_STATE_WAIT_IDENTIFY_NS;
        LOG_NVME("Submitted Identify Namespace, waiting...\n");
        break;
    }

    case NVME_STATE_WAIT_IDENTIFY_NS: {
        LOG_NVME("Identify Namespace completed\n");

        /*
         * FLBAS selects the active LBAF entry; LBADS gives sector size as 2^LBADS.
         * [NVM-CommandSet-1.1 §4.1.5.1, Fig. 114, Fig. 116]
         */
        uint8_t format_index = nvme_identify_flbas_format_index(nvme_identify_ns->flbas);
        uint8_t lbads UNUSED = nvme_identify_ns->lbaf[format_index].lbads;
        uint32_t sector_size = nvme_namespace_sector_size(nvme_identify_ns);

        /* Uses Logical Block Data Size only (2^LBADS); metadata size (MS) is excluded. [NVM-CommandSet-1.1 §1.4.2.5] */
        /* Extended LBA transfers (2^LBADS + MS) are currently not supported. [NVM-CommandSet-1.1 §1.4.3.1] */
        assert(BLK_TRANSFER_SIZE >= sector_size);
        assert(BLK_TRANSFER_SIZE % sector_size == 0);

        state_ctx.sectors_per_block = BLK_TRANSFER_SIZE / sector_size;
        uint64_t total_blocks UNUSED = (nvme_identify_ns->nsze * sector_size) / BLK_TRANSFER_SIZE;

        LOG_NVME("NS: NSZE=%lu, LBADS=%u, sector=%uB, capacity=%lu blocks\n", nvme_identify_ns->nsze, lbads,
                 sector_size, total_blocks);

        uint16_t io_queue_id = NVME_DEFAULT_IO_Q_ID;
        assert(nvme_io_sq_region != 0x0);
        assert(nvme_io_cq_region != 0x0);
        assert(nvme_io_sq_region_paddr != 0x0);
        assert(nvme_io_cq_region_paddr != 0x0);
        assert(state_ctx.io_queue_depth > 0);
        nvme_queues_init(&io_queue, io_queue_id, nvme_controller, nvme_io_sq_region, state_ctx.io_queue_depth,
                         nvme_io_cq_region, state_ctx.io_queue_depth);

        // §3.3.1.1 Queue Setup & Initialization
        // => Configures the size of the I/O Submission Queues (CC.IOSQES) and I/O Completion Queues (CC.IOCQES)
        /* n.b. CQ/SQ entry sizes are specified as 2^n; i.e. 2^4 = 16 and 2^6 = 64. */
        nvme_controller->cc &= ~(NVME_CC_IOCQES_MASK | NVME_CC_IOSQES_MASK);
        nvme_controller->cc |= ((uint32_t)NVME_HOST_IOCQES_EXP << NVME_CC_IOCQES_SHIFT)
                             | ((uint32_t)NVME_HOST_IOSQES_EXP << NVME_CC_IOSQES_SHIFT);

        // 10. Allocate the appropriate number of I/O Completion Queues [...]
        //     The I/O Completion Queues are allocated using the Create I/O Completion Queue command.
        // §5.2.1
        uint32_t admin_cid;
        int err = ialloc_alloc(&cid_ialloc, &admin_cid);
        assert(err == 0);
        assert(admin_cid <= UINT16_MAX);

        nvme_queue_submit(&admin_queue,
                          &(nvme_submission_queue_entry_t) {
                              .cdw0 = nvme_build_cdw0((uint16_t)admin_cid, NVME_ADMIN_OP_CREATE_IO_CQ, NVME_CDW0_PSDT_PRP),
                              .cdw10 = nvme_build_create_io_q_cdw10(NVME_DEFAULT_IO_Q_ID, state_ctx.io_queue_depth - 1U),
                              .cdw11 = nvme_build_create_io_cq_cdw11(NVME_CREATE_IO_Q_INTERRUPT_VECTOR, true, true),
                              .prp2 = 0,
                              .prp1 = nvme_io_cq_region_paddr,
                          });

        state_ctx.state = NVME_STATE_WAIT_CREATE_IO_CQ;
        LOG_NVME("Submitted Create I/O CQ, waiting for completion\n");
        break;
    }

    case NVME_STATE_WAIT_CREATE_IO_CQ: {
        LOG_NVME("Create I/O CQ completed\n");

        // 11. Allocate the appropriate number of I/O Submission Queues [...]
        //     The I/O Submission Queues are allocated using the Create I/O Submission Queue command.
        // §5.2.2
        uint32_t admin_cid;
        int err = ialloc_alloc(&cid_ialloc, &admin_cid);
        assert(err == 0);
        assert(admin_cid <= UINT16_MAX);

        nvme_queue_submit(&admin_queue,
                          &(nvme_submission_queue_entry_t) {
                              .cdw0 = nvme_build_cdw0((uint16_t)admin_cid, NVME_ADMIN_OP_CREATE_IO_SQ, NVME_CDW0_PSDT_PRP),
                              .cdw10 = nvme_build_create_io_q_cdw10(NVME_DEFAULT_IO_Q_ID, state_ctx.io_queue_depth - 1U),
                              .cdw11 = nvme_build_create_io_sq_cdw11(NVME_DEFAULT_IO_Q_ID, NVME_CREATE_IO_SQ_QPRIO_URGENT, true),
                              .cdw12 = 0,
                              .prp2 = 0,
                              .prp1 = nvme_io_sq_region_paddr,
                          });

        state_ctx.state = NVME_STATE_WAIT_CREATE_IO_SQ;
        LOG_NVME("Submitted Create I/O SQ, waiting for completion\n");
        break;
    }

    case NVME_STATE_WAIT_CREATE_IO_SQ: {
        LOG_NVME("Create I/O SQ completed\n");

        // 12. To enable asynchronous notification of optional events, the host should issue a Set Features
        // command specifying the events to enable. To enable asynchronous notification of events, the host
        // should submit an appropriate number of Asynchronous Event Request commands. This step may
        // be done at any point after the controller signals that the controller is ready (i.e., CSTS.RDY is set to '1').

        nvme_irq_unmask();

        blk_queue_init(&blk_queue, blk_config.virt.req_queue.vaddr, blk_config.virt.resp_queue.vaddr,
                       blk_config.virt.num_buffers);
        storage_info = blk_config.virt.storage_info.vaddr;

        /* Set storage info */
        storage_info->read_only = false;
        storage_info->sector_size = nvme_namespace_sector_size(nvme_identify_ns);
        storage_info->block_size = 1;
        storage_info->queue_depth = state_ctx.io_queue_depth;
        storage_info->cylinders = 0;
        storage_info->heads = 0;
        storage_info->blocks = 0;
        storage_info->capacity = (nvme_identify_ns->nsze * storage_info->sector_size) / BLK_TRANSFER_SIZE;

        copy_trim_ascii(storage_info->serial_number, sizeof(storage_info->serial_number),
                        (const char *)nvme_identify_ctrl->sn, sizeof(nvme_identify_ctrl->sn));

        LOG_NVME("Setting storage info ready at %p...\n", storage_info);
        blk_storage_set_ready(storage_info, true);

        state_ctx.state = NVME_STATE_READY;
        LOG_NVME("sDDF NVMe Driver Ready\n");
        break;
    }

    default:
        sddf_dprintf("Unexpected admin completion in state %d\n", state_ctx.state);
        break;
    }
}

static void handle_io_completions(void)
{
    nvme_completion_queue_entry_t cq_entry;
    bool notify = false;

    while (nvme_queue_consume(&io_queue, &cq_entry) == 0) {
        uint16_t cid = cq_entry.cid;
        if (cid >= state_ctx.io_queue_depth || !ialloc_in_use(&cid_ialloc, cid)) {
            sddf_dprintf("NVMe: completion with invalid CID=%u dropped\n", cid);
            continue;
        }

        uint32_t id = cid_to_id[cid];
        uint16_t count = cid_to_count[cid];
        uint16_t status = (cq_entry.phase_tag_and_status & NVME_CQE_STATUS_MASK) >> NVME_CQE_STATUS_SHIFT;

        /* Free the CID */
        int err = ialloc_free(&cid_ialloc, cid);
        assert(err == 0);

        blk_resp_status_t resp_status = (status == 0) ? BLK_RESP_OK : BLK_RESP_ERR_UNSPEC;
        /* Return the original requested count on success */
        err = blk_enqueue_resp(&blk_queue, resp_status, (resp_status == BLK_RESP_OK) ? count : 0, id);
        assert(!err);
        notify = true;
    }

    if (notify) {
        microkit_notify(blk_config.virt.id);
    }
}

static void handle_irq(void)
{
    if (state_ctx.state == NVME_STATE_READY) {
        handle_io_completions();
    } else {
        handle_admin_completions();
    }
}

static void nvme_poll_controller_status(void)
{
    LOG_NVME("state=%d\n", state_ctx.state);

    switch (state_ctx.state) {
    case NVME_STATE_WAIT_NOT_READY:
        // Wait for CSTS.RDY=0 (controller disabled)
        LOG_NVME("Waiting for NVMe controller to clear ready bit, timeout = %u...\n", state_ctx.timeout_ms);

        if (nvme_controller->csts & NVME_CSTS_RDY) {
            if (state_ctx.waited_ms < state_ctx.timeout_ms) {
                sddf_timer_set_timeout(timer_config.driver_id, NVME_CONTROLLER_STATUS_POLL_INTERVAL_NS);
                state_ctx.waited_ms += NVME_CONTROLLER_STATUS_POLL_INTERVAL_MS;
                return;
            }
            sddf_dprintf("NVMe reset timeout after %u ms\n", state_ctx.waited_ms);
            return;
        }
        LOG_NVME("controller reset complete\n");

        // 2. Configure Admin Queue(s); §3.5.1 steps 2-5
        nvme_queues_init(&admin_queue, 0, nvme_controller, nvme_asq_region, NVME_ASQ_CAPACITY, nvme_acq_region,
                         NVME_ACQ_CAPACITY);
        nvme_irq_mask();
        assert(nvme_asq_region_paddr != 0x0);
        assert(nvme_acq_region_paddr != 0x0);
        nvme_controller->asq = nvme_asq_region_paddr;
        nvme_controller->acq = nvme_acq_region_paddr;
        nvme_controller->aqa &= ~(NVME_AQA_ACQS_MASK | NVME_AQA_ASQS_MASK);
        nvme_controller->aqa |= ((NVME_ASQ_CAPACITY - 1) << NVME_AQA_ASQS_SHIFT)
                              | ((NVME_ACQ_CAPACITY - 1) << NVME_AQA_ACQS_SHIFT);

        // 3. Initialise Command Support Sets.
        // QEMU NVMe workaround: Always use NVM Command Set (CSS=0b000)
        // https://gitlab.com/qemu-project/qemu/-/issues/1691
        nvme_controller->cc &= ~(NVME_CC_CSS_MASK);
        nvme_controller->cc |= (NVME_CC_CSS_NVM << NVME_CC_CSS_SHIFT) & NVME_CC_CSS_MASK;

        // 4a. Arbitration Mechanism
        // 4b. Memory Page Size
        /* CAP.MPSMIN/MPSMAX bound host page size; minimum bytes = 2^(12 + MPSMIN). [NVMe-2.1 §3.1.4.1, Fig. 36] */
        uint8_t cap_mps_max = (nvme_controller->cap & NVME_CAP_MPSMAX_MASK) >> NVME_CAP_MPSMAX_SHIFT;
        uint8_t cap_mps_min = (nvme_controller->cap & NVME_CAP_MPSMIN_MASK) >> NVME_CAP_MPSMIN_SHIFT;

        // The maximum memory page size  is (2 ^ (12 + MPSMAX))
        assert(cap_mps_max >= (NVME_PAGE_SIZE_LOG2 - 12));

        // The minimum memory page size is (2 ^ (12 + MPSMIN))
        assert(cap_mps_min <= (NVME_PAGE_SIZE_LOG2 - 12));

        nvme_controller->cc &= ~NVME_CC_MPS_MASK;
        nvme_controller->cc |= ((NVME_PAGE_SIZE_LOG2 - 12) << NVME_CC_MPS_SHIFT) & NVME_CC_MPS_MASK;

        // 5. Enable the controller
        nvme_controller->cc |= NVME_CC_EN;

        // Transition to wait for ready (reset timeout per CAP.TO spec)
        state_ctx.waited_ms = 0;
        state_ctx.state = NVME_STATE_WAIT_READY;
        fallthrough;

    case NVME_STATE_WAIT_READY:
        // 6. Wait for ready
        LOG_NVME("Waiting for NVMe controller to set ready bit, timeout = %u...\n", state_ctx.timeout_ms);

        if (!(nvme_controller->csts & NVME_CSTS_RDY)) {
            if (state_ctx.waited_ms < state_ctx.timeout_ms) {
                sddf_timer_set_timeout(timer_config.driver_id, NVME_CONTROLLER_STATUS_POLL_INTERVAL_NS);
                state_ctx.waited_ms += NVME_CONTROLLER_STATUS_POLL_INTERVAL_MS;
                return;
            }
            sddf_dprintf("NVMe enable timeout after %u ms\n", state_ctx.waited_ms);
            return;
        }
        LOG_NVME("controller ready\n");

        // 7. Send the Identify Controller command (Identify with CNS = 01h); §5.1.13
        // Unmask interrupts before submitting admin commands
        nvme_irq_unmask();

        uint32_t admin_cid;
        int err = ialloc_alloc(&cid_ialloc, &admin_cid);
        assert(err == 0);
        assert(admin_cid <= UINT16_MAX);

        nvme_queue_submit(&admin_queue,
                          &(nvme_submission_queue_entry_t) {
                              .cdw0 = nvme_build_cdw0((uint16_t)admin_cid, NVME_ADMIN_OP_IDENTIFY, NVME_CDW0_PSDT_PRP),
                              .cdw10 = NVME_IDENTIFY_CNS_CONTROLLER,
                              .prp2 = 0,
                              .prp1 = NVME_IDENTIFY_CTRL_PADDR, /* Data region for identify - hardcoded for x86 */
                          });

        state_ctx.state = NVME_STATE_WAIT_IDENTIFY_CTRL;
        LOG_NVME("Submitted Identify Controller, waiting for completion\n");

        // Acknowledge any pending IRQ from controller ready
        sddf_irq_ack(NVME_IRQ);
        break;

    default:
        // Other transitions are IRQ-driven, so we shouldn't poll for these.
        assert(false);
        break;
    }
}

/* [NVMe-2.1] 3.5.1 Memory-based Controller Initialization (PCIe) */
void nvme_controller_init()
{
    LOG_NVME("CAP: %016lx\n", nvme_controller->cap);
    /* Read version as single 32-bit access to avoid unaligned device access. */
    uint32_t vs UNUSED = nvme_controller->vs;
    LOG_NVME("VS: major: %lu, minor: %lu, tertiary: %lu\n", (vs & NVME_VS_MJR) >> NVME_VS_MJR_SHIFT,
             (vs & NVME_VS_MNR) >> NVME_VS_MNR_SHIFT, (vs & NVME_VS_TER) >> NVME_VS_TER_SHIFT);
    LOG_NVME("CC: %08x\n", nvme_controller->cc);

    nvme_controller->cc &= ~NVME_CC_EN;

    // 1. Wait for CSTS.RDY to become '0' (i.e. not ready)
    /*
    [NVMe-2.1] Figure 36

    CAP.TO (offset 24)
    This is the worst-case time that host software should wait for the
    CSTS.RDY bit to transition from:`
    a) ‘0’ to ‘1’ after the CC.EN bit transitions from ‘0’ to ‘1’; or
    b) ‘1’ to ‘0’ after the CC.EN bit transitions from ‘1’ to ‘0’.
    This worst-case time may be experienced after events such as an abrupt shutdown,
    loss of main power without shutting down the controller, or activation of a new
    firmware image; typical times are expected to be much shorter.
    This field is in 500 millisecond units. The maximum value of this field is FFh, which
    indicates a 127.5 second timeout.
    */
    uint8_t cap_to = (uint8_t)((nvme_controller->cap & NVME_CAP_TO_MASK) >> NVME_CAP_TO_SHIFT);

    // Maximum Queue Entries Supported
    uint16_t mqes_raw = (uint16_t)(nvme_controller->cap & NVME_CAP_MQES_MASK);

    // Use uint32_t to avoid overflow if mqes_raw == 0xFFFF (0-based value means 65536 entries)
    uint32_t mqes_max = (uint32_t)mqes_raw + 1;
    uint32_t desired = NVME_IO_SQ_CAPACITY < NVME_IO_CQ_CAPACITY ? NVME_IO_SQ_CAPACITY : NVME_IO_CQ_CAPACITY;

    // Initialize state machine context
    state_ctx = (nvme_state_ctx_t) {
        .state = NVME_STATE_WAIT_NOT_READY,
        .timeout_ms = (cap_to + 1) * 500,
        .waited_ms = 0,
        .io_queue_depth = (mqes_max < desired) ? mqes_max : desired,
    };

    LOG_NVME("MQES: raw=0x%x -> max %u entries, using %u\n", mqes_raw, mqes_max, state_ctx.io_queue_depth);

    nvme_poll_controller_status();
}

void init(void)
{
    LOG_NVME("Initializing NVMe Driver...\n");

    /* Validate device_resources */
    assert(device_resources_check_magic(&device_resources));
    assert(blk_config_check_magic(&blk_config));
    assert(timer_config_check_magic(&timer_config));

    /* Check device presence first */
    uint32_t vid_did UNUSED = pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_ID);
    LOG_NVME("VendorID:DeviceID = %08x\n", vid_did);

    uint32_t bar0 UNUSED = pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_BAR0);
    LOG_NVME("NVMe PCI BAR0 readback: %08x\n", bar0);

    /* Enable Bus Master and Memory Space */
    uint32_t cmd = pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_COMMAND);
    pci_config_write_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_COMMAND, cmd | 0x6);
    LOG_NVME("PCI Command Register: %08x\n", pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_COMMAND));

    /* Check Interrupt Configuration */
    uint32_t intr_info = pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_INTR_INFO);
    uint8_t intr_line UNUSED = intr_info & NVME_PCIE_INTR_LINE_MASK;
    uint8_t intr_pin UNUSED = (intr_info & NVME_PCIE_INTR_PIN_MASK) >> NVME_PCIE_INTR_PIN_SHIFT;
    LOG_NVME("PCI Interrupt Line: %d, Pin: %d\n", intr_line, intr_pin);

    /* Map Controller and Metadata - x86 uses hardcoded addresses */
    nvme_controller = (void *)NVME_CONTROLLER_VADDR;

    nvme_asq_region = (void *)NVME_ASQ_VADDR;
    nvme_asq_region_paddr = NVME_ASQ_PADDR;

    nvme_acq_region = (void *)NVME_ACQ_VADDR;
    nvme_acq_region_paddr = NVME_ACQ_PADDR;

    nvme_io_sq_region = (void *)NVME_IO_SQ_VADDR;
    nvme_io_sq_region_paddr = NVME_IO_SQ_PADDR;

    nvme_io_cq_region = (void *)NVME_IO_CQ_VADDR;
    nvme_io_cq_region_paddr = NVME_IO_CQ_PADDR;

    nvme_identify_ctrl = (void *)NVME_IDENTIFY_CTRL_VADDR;
    nvme_identify_ns = (void *)NVME_IDENTIFY_NS_VADDR;

    /* Initialise CID allocator */
    ialloc_init(&cid_ialloc, cid_ialloc_idxlist, MAX_PENDING_REQS);

    /* NVMe Controller Init */
    nvme_controller_init();
}

void notified(microkit_channel ch)
{
    if (ch == NVME_IRQ) {
        /* Guard against early IRQ delivery before admin queues are initialised. */
        if (state_ctx.state > NVME_STATE_WAIT_READY) {
            handle_irq();
        }
        sddf_irq_ack(ch);
        return;
    }

    if (state_ctx.state != NVME_STATE_READY) {
        if (ch == timer_config.driver_id) {
            nvme_poll_controller_status();
        }
        return;
    }

    if (ch == blk_config.virt.id) {
        handle_request();
    } else {
        LOG_NVME("Unknown notification ch=%d\n", ch);
    }
}
