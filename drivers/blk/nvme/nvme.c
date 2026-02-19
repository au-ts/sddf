/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <stdint.h>
#include <string.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/config.h>
#include <sddf/blk/storage_info.h>
#include <sddf/util/util.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include <sddf/timer/config.h>
#include <sddf/timer/client.h>

#include "nvme_cmd.h"
#include "nvme_identify.h"
#include "nvme_pcie.h"
#include "nvme_platform.h"
#include "nvme_queue.h"

//#define DEBUG_DRIVER
#ifdef DEBUG_DRIVER
#include "nvme_debug.h"
#define UNUSED
#else
#define LOG_NVME(...)
#define UNUSED __attribute__((unused))
#endif

/* NVMe and PCIe are little-endian. [NVMe-2.1 §1.4.3] */
#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "code assumes little endian CPU as NVMe/PCIe is little endian"
#endif

#define fallthrough __attribute__((__fallthrough__))

/* Timed polling used while waiting for controller reset/enable transitions. */
#define NVME_CONTROLLER_STATUS_POLL_INTERVAL_MS 10U
#define NVME_CONTROLLER_STATUS_POLL_INTERVAL_NS (NVME_CONTROLLER_STATUS_POLL_INTERVAL_MS * NS_IN_MS)

/* Admin queue has ID 0 [NVMe-2.1 §1.5.4]; I/O queues use IDs 1-65535. [NVMe-2.1 §3.3.3.2] */
/* Only one I/O queue pair is supported and share ID 1. */
#define NVME_DEFAULT_IO_Q_ID 1U
/* One IV corresponds to one I/O queue pair. [NVMe-2.1 §5.2.1, Fig. 475] */
#define NVME_CREATE_IO_Q_INTERRUPT_VECTOR 0U

/* Valid NSIDs are 1h through FFFFFFFFh. [NVMe-2.1 §3.2.1.1] */
/* Only a single namespace is supported. */
#define NVME_DEFAULT_NSID 1U

/* Queue structures must fit their dedicated queue regions. */
_Static_assert(NVME_ADMIN_QUEUE_SIZE_BYTES <= NVME_ASQ_REGION_SIZE, "ASQ allocation exceeds nvme_admin_sq region size");
_Static_assert(NVME_ADMIN_QUEUE_SIZE_BYTES <= NVME_ACQ_REGION_SIZE, "ACQ allocation exceeds nvme_admin_cq region size");
_Static_assert(NVME_IO_QUEUE_SIZE_BYTES <= NVME_IO_SQ_REGION_SIZE, "IO SQ allocation exceeds nvme_io_sq region size");
_Static_assert(NVME_IO_QUEUE_SIZE_BYTES <= NVME_IO_CQ_REGION_SIZE, "IO CQ allocation exceeds nvme_io_cq region size");

#define NVME_ASQ_CAPACITY (NVME_ASQ_REGION_SIZE / sizeof(nvme_submission_queue_entry_t))
#define NVME_ACQ_CAPACITY (NVME_ACQ_REGION_SIZE / sizeof(nvme_completion_queue_entry_t))
#define NVME_IO_SQ_CAPACITY (NVME_IO_SQ_REGION_SIZE / sizeof(nvme_submission_queue_entry_t))
#define NVME_IO_CQ_CAPACITY (NVME_IO_CQ_REGION_SIZE / sizeof(nvme_completion_queue_entry_t))

/* Admin queue max 4096 entries, I/O queue max 65536 entries. [NVMe-2.1 §3.3.3.1] */
_Static_assert(NVME_ASQ_CAPACITY <= 0x1000, "capacity of ASQ must be <=4096 (entries)");
_Static_assert(NVME_ACQ_CAPACITY <= 0x1000, "capacity of ACQ must be <=4096 (entries)");
_Static_assert(NVME_IO_SQ_CAPACITY <= 0x10000, "capacity of IO SQ must be <=65536 (entries)");
_Static_assert(NVME_IO_CQ_CAPACITY <= 0x10000, "capacity of IO CQ must be <=65536 (entries)");

/* Identify buffers must fit in their shared region and not overlap. */
_Static_assert(NVME_IDENTIFY_CTRL_VADDR + sizeof(nvme_identify_ctrl_t) <= NVME_IDENTIFY_NS_VADDR,
               "Identify Controller buffer must not overlap Identify Namespace buffer");
_Static_assert(NVME_IDENTIFY_NS_VADDR + sizeof(nvme_identify_ns_t) <= NVME_IDENTIFY_VADDR + NVME_IDENTIFY_REGION_SIZE,
               "Identify Namespace buffer must fit within nvme_identify region");
_Static_assert(sizeof(nvme_identify_ctrl_t) <= NVME_IDENTIFY_BUFFER_BYTES,
               "Identify Controller structure must fit within one Identify buffer");
_Static_assert(sizeof(nvme_identify_ns_t) <= NVME_IDENTIFY_BUFFER_BYTES,
               "Identify Namespace structure must fit within one Identify buffer");
_Static_assert((2U * NVME_IDENTIFY_BUFFER_BYTES) <= NVME_IDENTIFY_REGION_SIZE,
               "NVMe identify region must fit both Identify buffers");

/* Map sDDF IDs to NVMe CIDs - align with I/O queue depth upper bound. */
#define NVME_MAX_PENDING_REQS NVME_IO_SQ_CAPACITY

/* SGL Data Block (SQE-inlined) needs no per-request memory; max is the blk_req_t count field width. */
#define NVME_SGL_MAX_INLINE_PAGES   UINT16_MAX

/*
 * PRP list model used by this driver (single, non-chained list page).
 * Each PRP entry is 8 bytes. [NVMe-2.1 §4.3.1]
 * Each request gets one slot (one host page).
 * PRP1 carries the first data page; PRP2 is either the second page (2-page I/O)
 * or a PRP list pointer (3+ page I/O). [NVMe-2.1 §4.1.1, Fig. 92]
 */
#define NVME_PRP_SLOT_SIZE              BLK_TRANSFER_SIZE
#define NVME_PRP_ENTRIES_PER_PAGE       ((uint32_t)(NVME_PRP_SLOT_SIZE / sizeof(uint64_t)))
#define NVME_PRP_NON_CHAINED_MAX_PAGES  (1U + NVME_PRP_ENTRIES_PER_PAGE) // PRP1 + List slot

_Static_assert((NVME_MAX_PENDING_REQS) * (NVME_PRP_SLOT_SIZE) <= NVME_PRP_SLOTS_REGION_SIZE,
               "PRP slot region exceeds configured nvme_prp_slots region size");

/*
 * Host queue entry-size exponents for CC.IOSQES/CC.IOCQES.
 * CC stores n where entry size is 2^n; Identify SQES/CQES report valid ranges.
 * [NVMe-2.1 §3.1.4.5; §5.1.13.2.1, Fig. 312]
 */
#define NVME_HOST_IOSQES_EXP ((uint8_t)__builtin_ctz((unsigned int)sizeof(nvme_submission_queue_entry_t)))
#define NVME_HOST_IOCQES_EXP ((uint8_t)__builtin_ctz((unsigned int)sizeof(nvme_completion_queue_entry_t)))
_Static_assert(NVME_HOST_IOSQES_EXP == 6, "Common SQE layout requires 64-byte entries (2^6)");
_Static_assert(NVME_HOST_IOCQES_EXP == 4, "Common CQE layout requires 16-byte entries (2^4)");

/*
 * State machine flow:
 *   WAIT_NOT_READY -> WAIT_READY -> WAIT_IDENTIFY_CTRL (timer-driven, see poll_controller_status)
 *   WAIT_IDENTIFY_CTRL -> WAIT_IDENTIFY_NS -> WAIT_CREATE_IO_CQ -> WAIT_CREATE_IO_SQ -> READY (IRQ-driven, see process_admin_completions)
 */
typedef enum {
    NVME_STATE_WAIT_NOT_READY,
    NVME_STATE_WAIT_READY,
    NVME_STATE_WAIT_IDENTIFY_CTRL,
    NVME_STATE_WAIT_IDENTIFY_NS,
    NVME_STATE_WAIT_CREATE_IO_CQ,
    NVME_STATE_WAIT_CREATE_IO_SQ,
    NVME_STATE_READY,
} nvme_init_state_t;

typedef struct {
    volatile nvme_controller_t *controller;

    nvme_submission_queue_entry_t *asq_region;
    nvme_completion_queue_entry_t *acq_region;
    uintptr_t asq_region_paddr;
    uintptr_t acq_region_paddr;

    nvme_submission_queue_entry_t *io_sq_region;
    nvme_completion_queue_entry_t *io_cq_region;
    uintptr_t io_sq_region_paddr;
    uintptr_t io_cq_region_paddr;

    nvme_identify_ctrl_t *identify_ctrl;
    nvme_identify_ns_t *identify_ns;
} nvme_hw_ctx_t;

typedef struct {
    nvme_init_state_t init_state;
    uint32_t timeout_ms;
    uint32_t waited_ms;

    uint8_t cap_mpsmin;
    uint16_t io_queue_depth;
    uint32_t sectors_per_block;
    uint32_t max_io_pages;
    bool use_sgl;
    bool sgl_requires_dword_align;
} nvme_runtime_ctx_t;

typedef struct {
    nvme_queue_info_t admin_queue;
    nvme_queue_info_t io_queue;

    blk_queue_handle_t blk_queue;
    blk_storage_info_t *storage_info;
} nvme_queues_ctx_t;

typedef struct {
    ialloc_t allocator;
    uint32_t idxlist[NVME_MAX_PENDING_REQS];
    uint32_t request_id_by_cid[NVME_MAX_PENDING_REQS];
    uint16_t page_count_by_cid[NVME_MAX_PENDING_REQS];
} nvme_cid_ctx_t;

typedef struct {
    nvme_hw_ctx_t hw;
    nvme_runtime_ctx_t runtime;
    nvme_queues_ctx_t queues;
    nvme_cid_ctx_t cid;
} nvme_driver_ctx_t;

static nvme_driver_ctx_t nvme_ctx;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".blk_driver_config"))) blk_driver_config_t blk_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

/* [NVMe-2.1 §3.1.4.3] */
static void nvme_irq_mask(nvme_driver_ctx_t *ctx)
{
    ctx->hw.controller->intms = 0xffffffff;
}

/* [NVMe-2.1 §3.1.4.4] */
static void nvme_irq_unmask(nvme_driver_ctx_t *ctx)
{
    /* Unmask vector 0 only. */
    ctx->hw.controller->intmc = BIT(0);
}

/* Ensure host SQE/CQE entry sizes fall within controller-advertised limits. */
static void validate_identify_entry_size_limits(nvme_driver_ctx_t *ctx)
{
    /* SQES/CQES bytes encode min/max 2^n entry-size bounds. [NVMe-2.1 Fig. 312] */
    uint8_t minsqes = (ctx->hw.identify_ctrl->sqes & NVME_IDENTIFY_ENTRY_SIZE_MIN_MASK)
                   >> NVME_IDENTIFY_ENTRY_SIZE_MIN_SHIFT;
    uint8_t maxsqes = (ctx->hw.identify_ctrl->sqes & NVME_IDENTIFY_ENTRY_SIZE_MAX_MASK)
                   >> NVME_IDENTIFY_ENTRY_SIZE_MAX_SHIFT;
    uint8_t mincqes = (ctx->hw.identify_ctrl->cqes & NVME_IDENTIFY_ENTRY_SIZE_MIN_MASK)
                   >> NVME_IDENTIFY_ENTRY_SIZE_MIN_SHIFT;
    uint8_t maxcqes = (ctx->hw.identify_ctrl->cqes & NVME_IDENTIFY_ENTRY_SIZE_MAX_MASK)
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

    LOG_NVME("SQES range [%u, %u], using IOSQES=%u; CQES range [%u, %u], using IOCQES=%u\n", minsqes, maxsqes,
             NVME_HOST_IOSQES_EXP, mincqes, maxcqes, NVME_HOST_IOCQES_EXP);
}

/* Resolve namespace logical-sector size from active FLBAS/LBAF selection. */
static uint32_t nvme_namespace_sector_size(const nvme_identify_ns_t *identify_ns)
{
    uint8_t format_index = nvme_identify_flbas_format_index(identify_ns->flbas);
    uint8_t lbads = identify_ns->lbaf[format_index].lbads;

    /* Logical block data size (sector size) = 2^LBADS bytes. */
    assert(lbads >= 9);
    return 1U << lbads;
}

/* Copy fixed-width ASCII fields and trim trailing space padding in place. */
static void copy_trim_ascii(char *dst, size_t dst_size, const char *src, size_t src_size)
{
    assert(dst_size >= (src_size + 1U));

    memcpy(dst, src, src_size);
    dst[src_size] = '\0';

    while (src_size > 0U && dst[src_size - 1U] == ' ') {
        dst[src_size - 1U] = '\0';
        src_size--;
    }
}

/* Bind context pointers to the statically mapped NVMe MMIO/DMA regions. */
static void nvme_map_hw_regions(nvme_driver_ctx_t *ctx)
{
    ctx->hw.controller = (void *)NVME_CONTROLLER_VADDR;

    ctx->hw.asq_region = (void *)NVME_ASQ_VADDR;
    ctx->hw.asq_region_paddr = NVME_ASQ_PADDR;

    ctx->hw.acq_region = (void *)NVME_ACQ_VADDR;
    ctx->hw.acq_region_paddr = NVME_ACQ_PADDR;

    ctx->hw.io_sq_region = (void *)NVME_IO_SQ_VADDR;
    ctx->hw.io_sq_region_paddr = NVME_IO_SQ_PADDR;

    ctx->hw.io_cq_region = (void *)NVME_IO_CQ_VADDR;
    ctx->hw.io_cq_region_paddr = NVME_IO_CQ_PADDR;

    ctx->hw.identify_ctrl = (void *)NVME_IDENTIFY_CTRL_VADDR;
    ctx->hw.identify_ns = (void *)NVME_IDENTIFY_NS_VADDR;
}

/* Build a single inline SGL Data Block descriptor for a contiguous buffer. */
static int build_sgl_dptr(const nvme_driver_ctx_t *ctx, uintptr_t data_paddr, uint32_t byte_count, uint64_t *dptr1,
                          uint64_t *dptr2)
{
    /* Enforce SGL dword alignment only when required by controller. */
    if (ctx->runtime.sgl_requires_dword_align
        && ((data_paddr | (uint64_t)byte_count) & NVME_SGL_DWORD_ALIGN_MASK) != 0) {
        sddf_dprintf("NVMe: SGL alignment violation: addr=0x%lx len=%u\n", data_paddr, byte_count);
        return -1;
    }

    uint8_t id = NVME_SGL_ID(NVME_SGL_TYPE_DATA_BLOCK, NVME_SGL_SUBTYPE_ADDRESS);

    *dptr1 = data_paddr;
    *dptr2 = (uint64_t)byte_count | ((uint64_t)id << NVME_SGL_DPTR2_ID_SHIFT);
    return 0;
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

    *dptr1 = data_paddr;
    *dptr2 = 0;

    if (count == 2) {
        *dptr2 = data_paddr + BLK_TRANSFER_SIZE;
    } else if (count > 2) {
        uint64_t *prp_list = (uint64_t *)(NVME_PRP_SLOTS_VADDR + (uint64_t)cid * NVME_PRP_SLOT_SIZE);
        uint64_t prp_list_paddr = NVME_PRP_SLOTS_PADDR + (uint64_t)cid * NVME_PRP_SLOT_SIZE;

        for (uint16_t i = 1; i < count; i++) {
            prp_list[i - 1] = data_paddr + ((uint64_t)i * BLK_TRANSFER_SIZE);
        }

        *dptr2 = prp_list_paddr;
    }

    return 0;
}

/*
 * Entry condition: init_state is WAIT_NOT_READY or WAIT_READY and this helper is
 * called from init() or timer notifications.
 * Exit condition: transitions to an IRQ-driven admin state after Identify submit,
 * or remains in polling states with a timer re-armed.
 */
static void poll_controller_status(nvme_driver_ctx_t *ctx)
{
    LOG_NVME("state=%d\n", ctx->runtime.init_state);

    switch (ctx->runtime.init_state) {
    case NVME_STATE_WAIT_NOT_READY:
        LOG_NVME("Waiting for NVMe controller to clear ready bit, timeout = %u...\n", ctx->runtime.timeout_ms);

        if (ctx->hw.controller->csts & NVME_CSTS_RDY) {
            if (ctx->runtime.waited_ms < ctx->runtime.timeout_ms) {
                sddf_timer_set_timeout(timer_config.driver_id, NVME_CONTROLLER_STATUS_POLL_INTERVAL_NS);
                ctx->runtime.waited_ms += NVME_CONTROLLER_STATUS_POLL_INTERVAL_MS;
                return;
            }
            sddf_dprintf("NVMe reset timeout after %u ms\n", ctx->runtime.waited_ms);
            return;
        }
        LOG_NVME("controller reset complete\n");

        nvme_queues_init(&ctx->queues.admin_queue, 0, ctx->hw.controller, ctx->hw.asq_region, NVME_ASQ_CAPACITY,
                         ctx->hw.acq_region, NVME_ACQ_CAPACITY);
        nvme_irq_mask(ctx);

        assert(ctx->hw.asq_region_paddr != 0x0);
        assert(ctx->hw.acq_region_paddr != 0x0);
        ctx->hw.controller->asq = ctx->hw.asq_region_paddr;
        ctx->hw.controller->acq = ctx->hw.acq_region_paddr;
        ctx->hw.controller->aqa &= ~(NVME_AQA_ACQS_MASK | NVME_AQA_ASQS_MASK);
        ctx->hw.controller->aqa |= ((uint32_t)(NVME_ASQ_CAPACITY - 1U) << NVME_AQA_ASQS_SHIFT)
                                 | ((uint32_t)(NVME_ACQ_CAPACITY - 1U) << NVME_AQA_ACQS_SHIFT);

        /* QEMU workaround: force NVM command set selection. */
        ctx->hw.controller->cc &= ~(NVME_CC_CSS_MASK);
        ctx->hw.controller->cc |= (NVME_CC_CSS_NVM << NVME_CC_CSS_SHIFT) & NVME_CC_CSS_MASK;

        /* CAP.MPSMIN/MPSMAX bound host page size; minimum bytes = 2^(12 + MPSMIN). [NVMe-2.1 §3.1.4.1, Fig. 36] */
        uint8_t cap_mps_max = (ctx->hw.controller->cap & NVME_CAP_MPSMAX_MASK) >> NVME_CAP_MPSMAX_SHIFT;
        uint8_t cap_mps_min = (ctx->hw.controller->cap & NVME_CAP_MPSMIN_MASK) >> NVME_CAP_MPSMIN_SHIFT;
        ctx->runtime.cap_mpsmin = cap_mps_min;

        assert(cap_mps_max >= (NVME_PAGE_SIZE_LOG2 - 12U));
        assert(cap_mps_min <= (NVME_PAGE_SIZE_LOG2 - 12U));

        ctx->hw.controller->cc &= ~NVME_CC_MPS_MASK;
        ctx->hw.controller->cc |= ((NVME_PAGE_SIZE_LOG2 - 12U) << NVME_CC_MPS_SHIFT) & NVME_CC_MPS_MASK;

        ctx->hw.controller->cc |= NVME_CC_EN;

        ctx->runtime.waited_ms = 0;
        ctx->runtime.init_state = NVME_STATE_WAIT_READY;
        fallthrough;

    case NVME_STATE_WAIT_READY:
        LOG_NVME("Waiting for NVMe controller to set ready bit, timeout = %u...\n", ctx->runtime.timeout_ms);

        if (!(ctx->hw.controller->csts & NVME_CSTS_RDY)) {
            if (ctx->runtime.waited_ms < ctx->runtime.timeout_ms) {
                sddf_timer_set_timeout(timer_config.driver_id, NVME_CONTROLLER_STATUS_POLL_INTERVAL_NS);
                ctx->runtime.waited_ms += NVME_CONTROLLER_STATUS_POLL_INTERVAL_MS;
                return;
            }
            sddf_dprintf("NVMe enable timeout after %u ms\n", ctx->runtime.waited_ms);
            return;
        }
        LOG_NVME("controller ready\n");

        nvme_irq_unmask(ctx);
        uint32_t admin_cid;
        int err = ialloc_alloc(&ctx->cid.allocator, &admin_cid);
        assert(err == 0);
        assert(admin_cid <= UINT16_MAX);

        /* Identify data response is 4096 bytes via DPTR.
         * [NVMe-2.1 §5.1.13, Fig. 306]
         */
        nvme_queue_submit(&ctx->queues.admin_queue,
                          &(nvme_submission_queue_entry_t) {
                              .cdw0 = nvme_build_cdw0((uint16_t)admin_cid, NVME_ADMIN_OP_IDENTIFY, NVME_CDW0_PSDT_PRP),
                              .cdw10 = NVME_IDENTIFY_CNS_CONTROLLER,
                              .dptr2 = 0,
                              .dptr1 = NVME_IDENTIFY_CTRL_PADDR,
                          });

        ctx->runtime.init_state = NVME_STATE_WAIT_IDENTIFY_CTRL;
        LOG_NVME("Submitted Identify Controller, waiting for completion\n");
        sddf_irq_ack(NVME_IRQ);
        break;

    default:
        assert(false);
        break;
    }
}

/* Seed controller init runtime state, then start the reset/enable polling sequence. */
static void nvme_controller_init(nvme_driver_ctx_t *ctx)
{
    LOG_NVME("CAP: %016lx\n", ctx->hw.controller->cap);

    uint32_t vs UNUSED = ctx->hw.controller->vs;
    LOG_NVME("VS: major: %lu, minor: %lu, tertiary: %lu\n", (vs & NVME_VS_MJR_MASK) >> NVME_VS_MJR_SHIFT,
             (vs & NVME_VS_MNR_MASK) >> NVME_VS_MNR_SHIFT, (vs & NVME_VS_TER_MASK) >> NVME_VS_TER_SHIFT);
    LOG_NVME("CC: %08x\n", ctx->hw.controller->cc);

    /* Clear CC.EN to begin controller reset; wait for CSTS.RDY to clear. [NVMe-2.1 §3.5.2] */
    ctx->hw.controller->cc &= ~NVME_CC_EN;

    uint8_t cap_to = (uint8_t)((ctx->hw.controller->cap & NVME_CAP_TO_MASK) >> NVME_CAP_TO_SHIFT);

    uint16_t mqes_raw = (uint16_t)(ctx->hw.controller->cap & NVME_CAP_MQES_MASK);
    uint16_t mqes_max = (uint16_t)(mqes_raw + 1U);
    uint16_t desired = NVME_IO_SQ_CAPACITY < NVME_IO_CQ_CAPACITY ? NVME_IO_SQ_CAPACITY : NVME_IO_CQ_CAPACITY;

    ctx->runtime.io_queue_depth = (mqes_max < desired) ? mqes_max : desired;
    LOG_NVME("MQES: raw=0x%x -> max %u entries, using %u\n", mqes_raw, mqes_max, ctx->runtime.io_queue_depth);
    ialloc_init(&ctx->cid.allocator, ctx->cid.idxlist, ctx->runtime.io_queue_depth);

    ctx->runtime.init_state = NVME_STATE_WAIT_NOT_READY;
    /* CAP.TO specifies worst-case timeout in 500 ms units. [NVMe-2.1 §3.1.4.1, Fig. 36] */
    ctx->runtime.timeout_ms = (uint32_t)(cap_to) * 500U;
    ctx->runtime.waited_ms = 0;

    poll_controller_status(ctx);
}

/*
 * Entry condition: blk virtualiser has notified with pending requests and driver
 * is in READY state.
 * Exit condition: all currently queued requests are submitted or completed with
 * immediate error responses.
 */
static void process_blk_requests(nvme_driver_ctx_t *ctx)
{
    bool notify_virt = false;

    blk_req_code_t code;
    uintptr_t req_paddr;
    uint64_t block_number;
    uint16_t count;
    uint32_t id;

    while (true) {
        if (ialloc_num_free(&ctx->cid.allocator) == 0U) {
            LOG_NVME("No free CIDs, deferring request dequeue until completions free slots\n");
            break;
        }

        int err = blk_dequeue_req(&ctx->queues.blk_queue, &code, &req_paddr, &block_number, &count, &id);
        if (err != 0) {
            break;
        }

        uint8_t opcode = 0;

        switch (code) {
        case BLK_REQ_READ:
            opcode = NVME_OP_READ;
            break;
        case BLK_REQ_WRITE:
            opcode = NVME_OP_WRITE;
            break;
        case BLK_REQ_FLUSH: {
            uint32_t cid;
            err = ialloc_alloc(&ctx->cid.allocator, &cid);
            assert(err == 0);
            ctx->cid.request_id_by_cid[cid] = id;
            ctx->cid.page_count_by_cid[cid] = 0;

            nvme_queue_submit(&ctx->queues.io_queue,
                              &(nvme_submission_queue_entry_t) {
                                  .cdw0 = nvme_build_cdw0((uint16_t)cid, NVME_OP_FLUSH, NVME_CDW0_PSDT_PRP),
                                  .nsid = NVME_DEFAULT_NSID,
                              });

            LOG_NVME("Submitted FLUSH: cid=%u req_id=%u\n", cid, id);
            continue;
        }
        case BLK_REQ_BARRIER:
            err = blk_enqueue_resp(&ctx->queues.blk_queue, BLK_RESP_OK, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        default:
            err = blk_enqueue_resp(&ctx->queues.blk_queue, BLK_RESP_ERR_INVALID_PARAM, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        }

        if (count == 0) {
            sddf_dprintf("NVMe: rejecting zero-length request\n");
            err = blk_enqueue_resp(&ctx->queues.blk_queue, BLK_RESP_ERR_INVALID_PARAM, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        }

        /* Reject oversized transfers */
        if (count > ctx->runtime.max_io_pages) {
            sddf_dprintf("NVMe: request too large (%u pages, max %u)\n", count, ctx->runtime.max_io_pages);
            err = blk_enqueue_resp(&ctx->queues.blk_queue, BLK_RESP_ERR_UNSPEC, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        }

        uint64_t lba = block_number * ctx->runtime.sectors_per_block;
        uint32_t nlb = (count * ctx->runtime.sectors_per_block) - 1U;

        uint32_t cid;
        err = ialloc_alloc(&ctx->cid.allocator, &cid);
        assert(err == 0);
        ctx->cid.request_id_by_cid[cid] = id;
        ctx->cid.page_count_by_cid[cid] = count;

        uint64_t dptr1 = 0;
        uint64_t dptr2 = 0;
        uint32_t cdw0;

        if (ctx->runtime.use_sgl) {
            cdw0 = nvme_build_cdw0((uint16_t)cid, opcode, NVME_CDW0_PSDT_SGL_MPTR_CONTIG);
            err = build_sgl_dptr(ctx, req_paddr, (uint32_t)count * BLK_TRANSFER_SIZE, &dptr1, &dptr2);
        } else {
            cdw0 = nvme_build_cdw0((uint16_t)cid, opcode, NVME_CDW0_PSDT_PRP);
            err = build_prp_dptr(cid, req_paddr, count, &dptr1, &dptr2);
        }

        if (err != 0) {
            err = ialloc_free(&ctx->cid.allocator, cid);
            assert(!err);
            err = blk_enqueue_resp(&ctx->queues.blk_queue, BLK_RESP_ERR_UNSPEC, 0, id);
            assert(!err);
            notify_virt = true;
            continue;
        }

        nvme_queue_submit(&ctx->queues.io_queue, &(nvme_submission_queue_entry_t) {
                                                     .cdw0 = cdw0,
                                                     .nsid = NVME_DEFAULT_NSID,
                                                     .cdw10 = (uint32_t)lba,
                                                     .cdw11 = (uint32_t)(lba >> 32),
                                                     .cdw12 = nvme_build_rw_cdw12(nlb, true),
                                                     .dptr1 = dptr1,
                                                     .dptr2 = dptr2,
                                                 });
    }

    if (notify_virt) {
        sddf_notify(blk_config.virt.id);
    }
}

/*
 * Entry condition: non-ready init state and an NVMe admin completion was signaled.
 * Exit condition: init_state advances toward READY or logs an admin error and
 * leaves the current state unchanged for diagnostics.
 */
static void process_admin_completions(nvme_driver_ctx_t *ctx)
{
    nvme_completion_queue_entry_t entry;

    if (nvme_queue_consume(&ctx->queues.admin_queue, &entry) != 0) {
        LOG_NVME("process_admin_completions: no completion available\n");
        return;
    }

    if (entry.cid >= ctx->runtime.io_queue_depth || !ialloc_in_use(&ctx->cid.allocator, entry.cid)) {
        sddf_dprintf("NVMe: admin completion with invalid CID=%u dropped\n", entry.cid);
        return;
    }

    int err = ialloc_free(&ctx->cid.allocator, entry.cid);
    assert(err == 0);

    uint16_t status = (entry.phase_tag_and_status & NVME_CQE_STATUS_MASK) >> NVME_CQE_STATUS_SHIFT;
    if (status != 0) {
        sddf_dprintf("NVMe admin command failed with status 0x%x in state %d\n", status, ctx->runtime.init_state);
        return;
    }

    LOG_NVME("Admin completion in state %d\n", ctx->runtime.init_state);

    switch (ctx->runtime.init_state) {
    case NVME_STATE_WAIT_IDENTIFY_CTRL: {
        LOG_NVME("Identify Controller completed\n");
        LOG_NVME("  VID: 0x%04x  SSVID: 0x%04x\n", ctx->hw.identify_ctrl->vid, ctx->hw.identify_ctrl->ssvid);
        LOG_NVME("  SN:  %.20s\n", (const char *)ctx->hw.identify_ctrl->sn);
        LOG_NVME("  MN:  %.40s\n", (const char *)ctx->hw.identify_ctrl->mn);
        LOG_NVME("  FR:  %.8s\n", (const char *)ctx->hw.identify_ctrl->fr);
        LOG_NVME("  SGLS: 0x%08x\n", ctx->hw.identify_ctrl->sgls);

        /*
         * SGL mode selection currently uses SGLS[1:0] (support + alignment class).
         * [NVMe-2.1 §5.1.13.2.1, Fig. 312]
         */
        uint32_t sgl_support = ctx->hw.identify_ctrl->sgls & NVME_IDENTIFY_SGLS_TRANSPORT_MASK;
        ctx->runtime.use_sgl = (sgl_support & NVME_IDENTIFY_SGLS_TRANSPORT_BYTE_ALIGNED)
                            || (sgl_support & NVME_IDENTIFY_SGLS_TRANSPORT_DWORD_ALIGNED);
        ctx->runtime.sgl_requires_dword_align = (sgl_support == NVME_IDENTIFY_SGLS_TRANSPORT_DWORD_ALIGNED);

        if (ctx->runtime.use_sgl) {
            LOG_NVME("I/O DPTR mode: SGL (%s alignment)\n", ctx->runtime.sgl_requires_dword_align ? "dword" : "byte");
        } else {
            LOG_NVME("I/O DPTR mode: PRP fallback (controller does not report SGL support)\n");
        }

        /*
         * MDTS scaling:
         * max transfer bytes = 2^MDTS * 2^(12 + CAP.MPSMIN), MDTS=0 means no limit.
         * [NVMe-2.1 §5.1.13.2.1, Fig. 312]
         */
        uint8_t mdts = ctx->hw.identify_ctrl->mdts;

        uint32_t static_max_pages = ctx->runtime.use_sgl ? NVME_SGL_MAX_INLINE_PAGES : NVME_PRP_ENTRIES_PER_PAGE;

        if (mdts == 0) {
            ctx->runtime.max_io_pages = static_max_pages;
            LOG_NVME("MDTS: controller has no limit, capping to %u pages\n", ctx->runtime.max_io_pages);
        } else {
            uint8_t shift = mdts + ctx->runtime.cap_mpsmin;
            uint32_t pages;

            if (shift >= 32U) {
                LOG_NVME("MDTS: raw=%u, MPSMIN=%u gives shift=%u (overflow)\n", mdts, ctx->runtime.cap_mpsmin, shift);
                pages = UINT32_MAX;
            } else {
                pages = 1U << (uint32_t)shift;
            }

            LOG_NVME("MDTS: raw=%u, MPSMIN=%u -> max %u pages (%u KiB)\n", mdts, ctx->runtime.cap_mpsmin, pages,
                     pages * 4);

            if (pages > static_max_pages) {
                LOG_NVME("MDTS: %u pages exceeds %s capacity (%u), clamping\n", pages,
                         ctx->runtime.use_sgl ? "SGL inline" : "PRP slot", static_max_pages);
                pages = static_max_pages;
            }

            ctx->runtime.max_io_pages = pages;
        }

        validate_identify_entry_size_limits(ctx);
        uint32_t admin_cid;
        err = ialloc_alloc(&ctx->cid.allocator, &admin_cid);
        assert(err == 0);
        assert(admin_cid <= UINT16_MAX);

        /*
         * Identify Namespace for the NVM Command Set (CNS=00h).
         * [NVM-CommandSet-1.1 §4.1.5.1, Fig. 114]
         */
        nvme_queue_submit(&ctx->queues.admin_queue,
                          &(nvme_submission_queue_entry_t) {
                              .cdw0 = nvme_build_cdw0((uint16_t)admin_cid, NVME_ADMIN_OP_IDENTIFY, NVME_CDW0_PSDT_PRP),
                              .nsid = NVME_DEFAULT_NSID,
                              .cdw10 = NVME_IDENTIFY_CNS_NAMESPACE,
                              .dptr1 = NVME_IDENTIFY_NS_PADDR,
                          });

        ctx->runtime.init_state = NVME_STATE_WAIT_IDENTIFY_NS;
        LOG_NVME("Submitted Identify Namespace (NSID=1), waiting...\n");
        break;
    }

    case NVME_STATE_WAIT_IDENTIFY_NS: {
        LOG_NVME("Identify Namespace completed\n");

        /*
         * FLBAS selects the active LBAF entry; LBADS gives sector size as 2^LBADS.
         * [NVM-CommandSet-1.1 §4.1.5.1, Fig. 114, Fig. 116]
         */
        uint8_t format_index = nvme_identify_flbas_format_index(ctx->hw.identify_ns->flbas);
        uint8_t lbads UNUSED = ctx->hw.identify_ns->lbaf[format_index].lbads;
        uint32_t sector_size = nvme_namespace_sector_size(ctx->hw.identify_ns);

        /* Uses Logical Block Data Size only (2^LBADS); metadata size (MS) is excluded. [NVM-CommandSet-1.1 §1.4.2.5] */
        /* Extended LBA transfers (2^LBADS + MS) are currently not supported. [NVM-CommandSet-1.1 §1.4.3.1] */
        assert(BLK_TRANSFER_SIZE >= sector_size);
        assert(BLK_TRANSFER_SIZE % sector_size == 0);

        ctx->runtime.sectors_per_block = BLK_TRANSFER_SIZE / sector_size;
        uint64_t total_blocks UNUSED = (ctx->hw.identify_ns->nsze * sector_size) / BLK_TRANSFER_SIZE;

        LOG_NVME("NS: NSZE=%lu, LBADS=%u, sector=%uB, capacity=%lu blocks\n", ctx->hw.identify_ns->nsze, lbads,
                 sector_size, total_blocks);

        assert(ctx->hw.io_sq_region != 0x0);
        assert(ctx->hw.io_cq_region != 0x0);
        assert(ctx->hw.io_sq_region_paddr != 0x0);
        assert(ctx->hw.io_cq_region_paddr != 0x0);
        assert(ctx->runtime.io_queue_depth > 0);

        nvme_queues_init(&ctx->queues.io_queue, NVME_DEFAULT_IO_Q_ID, ctx->hw.controller, ctx->hw.io_sq_region,
                         ctx->runtime.io_queue_depth, ctx->hw.io_cq_region, ctx->runtime.io_queue_depth);

        /* Program CC.IOCQES/CC.IOSQES as 2^n exponents before Create I/O Queue commands. [NVMe-2.1 §3.1.4.5] */
        ctx->hw.controller->cc &= ~(NVME_CC_IOCQES_MASK | NVME_CC_IOSQES_MASK);
        ctx->hw.controller->cc |= ((uint32_t)NVME_HOST_IOCQES_EXP << NVME_CC_IOCQES_SHIFT)
                                | ((uint32_t)NVME_HOST_IOSQES_EXP << NVME_CC_IOSQES_SHIFT);
        uint32_t admin_cid;
        err = ialloc_alloc(&ctx->cid.allocator, &admin_cid);
        assert(err == 0);
        assert(admin_cid <= UINT16_MAX);

        nvme_queue_submit(
            &ctx->queues.admin_queue,
            &(nvme_submission_queue_entry_t) {
                .cdw0 = nvme_build_cdw0((uint16_t)admin_cid, NVME_ADMIN_OP_CREATE_IO_CQ, NVME_CDW0_PSDT_PRP),
                .cdw10 = nvme_build_create_io_q_cdw10(NVME_DEFAULT_IO_Q_ID, ctx->runtime.io_queue_depth - 1U),
                .cdw11 = nvme_build_create_io_cq_cdw11(NVME_CREATE_IO_Q_INTERRUPT_VECTOR, true, true),
                .dptr2 = 0,
                .dptr1 = ctx->hw.io_cq_region_paddr,
            });

        ctx->runtime.init_state = NVME_STATE_WAIT_CREATE_IO_CQ;
        LOG_NVME("Submitted Create I/O CQ, waiting for completion\n");
        break;
    }

    case NVME_STATE_WAIT_CREATE_IO_CQ: {
        LOG_NVME("Create I/O CQ completed\n");
        uint32_t admin_cid;
        err = ialloc_alloc(&ctx->cid.allocator, &admin_cid);
        assert(err == 0);
        assert(admin_cid <= UINT16_MAX);

        nvme_queue_submit(
            &ctx->queues.admin_queue,
            &(nvme_submission_queue_entry_t) {
                .cdw0 = nvme_build_cdw0((uint16_t)admin_cid, NVME_ADMIN_OP_CREATE_IO_SQ, NVME_CDW0_PSDT_PRP),
                .cdw10 = nvme_build_create_io_q_cdw10(NVME_DEFAULT_IO_Q_ID, ctx->runtime.io_queue_depth - 1U),
                .cdw11 = nvme_build_create_io_sq_cdw11(NVME_DEFAULT_IO_Q_ID, NVME_CREATE_IO_SQ_QPRIO_URGENT, true),
                .cdw12 = 0,
                .dptr2 = 0,
                .dptr1 = ctx->hw.io_sq_region_paddr,
            });

        ctx->runtime.init_state = NVME_STATE_WAIT_CREATE_IO_SQ;
        LOG_NVME("Submitted Create I/O SQ, waiting for completion\n");
        break;
    }

    case NVME_STATE_WAIT_CREATE_IO_SQ: {
        LOG_NVME("Create I/O SQ completed\n");

        nvme_irq_unmask(ctx);

        blk_queue_init(&ctx->queues.blk_queue, blk_config.virt.req_queue.vaddr, blk_config.virt.resp_queue.vaddr,
                       blk_config.virt.num_buffers);
        ctx->queues.storage_info = blk_config.virt.storage_info.vaddr;

        copy_trim_ascii(ctx->queues.storage_info->serial_number, sizeof(ctx->queues.storage_info->serial_number),
                        (const char *)ctx->hw.identify_ctrl->sn, sizeof(ctx->hw.identify_ctrl->sn));

        ctx->queues.storage_info->read_only = false;
        /* Same derivation as above: sector_size = 2^LBADS from selected FLBAS/LBAF. [NVM-CommandSet-1.1 Fig. 114, Fig. 116] */
        ctx->queues.storage_info->sector_size = nvme_namespace_sector_size(ctx->hw.identify_ns);
        ctx->queues.storage_info->block_size = 1;
        ctx->queues.storage_info->queue_depth = ctx->runtime.io_queue_depth;
        ctx->queues.storage_info->cylinders = 0;
        ctx->queues.storage_info->heads = 0;
        ctx->queues.storage_info->blocks = 0;
        ctx->queues.storage_info->capacity = (ctx->hw.identify_ns->nsze * ctx->queues.storage_info->sector_size)
                                           / BLK_TRANSFER_SIZE;

        LOG_NVME("Setting storage info ready at %p...\n", ctx->queues.storage_info);
        blk_storage_set_ready(ctx->queues.storage_info, true);

        ctx->runtime.init_state = NVME_STATE_READY;
        LOG_NVME("sDDF NVMe Driver Ready\n");
        break;
    }

    default:
        sddf_dprintf("Unexpected admin completion in state %d\n", ctx->runtime.init_state);
        break;
    }
}

/*
 * Entry condition: READY state and one or more I/O completions are visible in
 * the I/O completion queue.
 * Exit condition: all currently visible completions are drained and corresponding
 * sDDF blk responses are queued.
 */
static void process_io_completions(nvme_driver_ctx_t *ctx)
{
    nvme_completion_queue_entry_t cq_entry;
    bool notify = false;

    while (nvme_queue_consume(&ctx->queues.io_queue, &cq_entry) == 0) {
        uint16_t cid = cq_entry.cid;
        if (cid >= ctx->runtime.io_queue_depth || !ialloc_in_use(&ctx->cid.allocator, cid)) {
            sddf_dprintf("NVMe: completion with invalid CID=%u dropped\n", cid);
            continue;
        }

        uint32_t id = ctx->cid.request_id_by_cid[cid];
        uint16_t count = ctx->cid.page_count_by_cid[cid];
        uint16_t status = (cq_entry.phase_tag_and_status & NVME_CQE_STATUS_MASK) >> NVME_CQE_STATUS_SHIFT;

        if (status != 0) {
            LOG_NVME("I/O completion error: cid=%u status=0x%x\n", cid, status);
        }

        int err = ialloc_free(&ctx->cid.allocator, cid);
        assert(err == 0);

        blk_resp_status_t resp_status = (status == 0) ? BLK_RESP_OK : BLK_RESP_ERR_UNSPEC;
        err = blk_enqueue_resp(&ctx->queues.blk_queue, resp_status, (resp_status == BLK_RESP_OK) ? count : 0, id);
        assert(!err);
        notify = true;
    }

    if (notify) {
        sddf_notify(blk_config.virt.id);
    }
}

/* Route an NVMe IRQ to admin-init or data-path completion handling by state. */
static void process_nvme_irq(nvme_driver_ctx_t *ctx)
{
    if (ctx->runtime.init_state == NVME_STATE_READY) {
        process_io_completions(ctx);
    } else {
        process_admin_completions(ctx);
    }
}

void init(void)
{
    nvme_driver_ctx_t *ctx = &nvme_ctx;

    LOG_NVME("Initializing NVMe Driver...\n");

    assert(device_resources_check_magic(&device_resources));
    assert(blk_config_check_magic(&blk_config));
    assert(timer_config_check_magic(&timer_config));

    uint32_t vid_did UNUSED = pci_config_read_32(NVME_PCI_CONFIG_ADDR_IOPORT_ID, NVME_PCI_CONFIG_DATA_IOPORT_ID,
                                                 NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_ID);
    LOG_NVME("VendorID:DeviceID = %08x\n", vid_did);

    uint32_t bar0 UNUSED = pci_config_read_32(NVME_PCI_CONFIG_ADDR_IOPORT_ID, NVME_PCI_CONFIG_DATA_IOPORT_ID,
                                              NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_BAR0);
    LOG_NVME("NVMe PCI BAR0 readback: %08x\n", bar0);

    uint32_t cmd = pci_config_read_32(NVME_PCI_CONFIG_ADDR_IOPORT_ID, NVME_PCI_CONFIG_DATA_IOPORT_ID, NVME_PCI_BUS,
                                      NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_COMMAND);
    cmd |= NVME_PCIE_COMMAND_BUS_MASTER_ENABLE | NVME_PCIE_COMMAND_MEMORY_SPACE_ENABLE;
    pci_config_write_32(NVME_PCI_CONFIG_ADDR_IOPORT_ID, NVME_PCI_CONFIG_DATA_IOPORT_ID, NVME_PCI_BUS, NVME_PCI_DEV,
                        NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_COMMAND, cmd);
    LOG_NVME("PCI Command Register: %08x\n",
             pci_config_read_32(NVME_PCI_CONFIG_ADDR_IOPORT_ID, NVME_PCI_CONFIG_DATA_IOPORT_ID, NVME_PCI_BUS,
                                NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_COMMAND));

    uint32_t intr_info = pci_config_read_32(NVME_PCI_CONFIG_ADDR_IOPORT_ID, NVME_PCI_CONFIG_DATA_IOPORT_ID,
                                            NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, NVME_PCIE_CFG_OFFSET_INTR_INFO);
    uint8_t intr_line UNUSED = intr_info & NVME_PCIE_INTR_LINE_MASK;
    uint8_t intr_pin UNUSED = (intr_info & NVME_PCIE_INTR_PIN_MASK) >> NVME_PCIE_INTR_PIN_SHIFT;
    LOG_NVME("PCI Interrupt Line: %d, Pin: %d\n", intr_line, intr_pin);

    nvme_map_hw_regions(ctx);

    nvme_controller_init(ctx);
}

void notified(microkit_channel ch)
{
    nvme_driver_ctx_t *ctx = &nvme_ctx;

    if (ch == NVME_IRQ) {
        /* Guard against early IRQ delivery before admin queues are initialised. */
        if (ctx->runtime.init_state > NVME_STATE_WAIT_READY) {
            process_nvme_irq(ctx);
        }
        sddf_irq_ack(ch);
        return;
    }

    if (ctx->runtime.init_state != NVME_STATE_READY) {
        if (ch == timer_config.driver_id) {
            poll_controller_status(ctx);
        }
        return;
    }

    if (ch == blk_config.virt.id) {
        process_blk_requests(ctx);
    } else {
        LOG_NVME("Unknown notification ch=%d\n", ch);
    }
}
