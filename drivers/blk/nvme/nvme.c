/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/config.h>
#include <sddf/blk/storage_info.h>
#include <sddf/util/util.h>
#include <sddf/resources/device.h>
#include <sddf/timer/config.h>
#include <sddf/timer/client.h>

#include "nvme.h"
#include "nvme_queue.h"

#define DEBUG_DRIVER
#ifdef DEBUG_DRIVER
#include "nvme_debug.h"
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
#define NVME_ADMIN_QUEUE_SIZE 0x1000
#define NVME_IO_QUEUE_SIZE    0x1000

static nvme_queue_info_t admin_queue;
static nvme_queue_info_t io_queue;

static blk_queue_handle_t blk_queue;
static blk_storage_info_t *storage_info;

/*
 * State machine flow:
 *   WAIT_NOT_READY -> WAIT_READY -> WAIT_IDENTIFY (timer-driven, see nvme_poll_controller_status)
 *   WAIT_IDENTIFY -> WAIT_CREATE_IO_CQ -> WAIT_CREATE_IO_SQ -> READY (IRQ-driven, see handle_admin_completions)
 */
typedef enum {
    NVME_STATE_WAIT_NOT_READY,    // Waiting for CSTS.RDY=0
    NVME_STATE_WAIT_READY,        // Waiting for CSTS.RDY=1
    NVME_STATE_WAIT_IDENTIFY,     // Waiting for Identify Controller completion
    NVME_STATE_WAIT_CREATE_IO_CQ, // Waiting for Create I/O CQ completion
    NVME_STATE_WAIT_CREATE_IO_SQ, // Waiting for Create I/O SQ completion
    NVME_STATE_READY,             // Operational
} nvme_state_t;

typedef struct {
    nvme_state_t state;
    uint32_t timeout_ms;   // CAP.TO derived timeout
    uint32_t waited_ms;    // Time waited in current state
} nvme_state_ctx_t;

static nvme_state_ctx_t state_ctx;

#define fallthrough __attribute__((__fallthrough__))

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".blk_driver_config"))) blk_driver_config_t blk_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

/*
 * PCI Configuration (hardcoded for x86_64)
 * FUTURE: Get these from PCIe enumeration
 */

#define NVME_PCI_BUS 0
#define NVME_PCI_DEV 4
#define NVME_PCI_FUNC 0

/* Memory Region Virtual Addresses */
#define NVME_CONTROLLER_VADDR (0x20000000)
#define NVME_METADATA_VADDR (0x20100000)
#define NVME_ASQ_VADDR (NVME_METADATA_VADDR + 0x0000)
#define NVME_ACQ_VADDR (NVME_METADATA_VADDR + 0x1000)
#define NVME_IO_SQ_VADDR (NVME_METADATA_VADDR + 0x2000)
#define NVME_IO_CQ_VADDR (NVME_METADATA_VADDR + 0x3000)
#define NVME_PRP_LIST_VADDR (NVME_METADATA_VADDR + 0x4000)
#define NVME_DATA_REGION_VADDR (0x20200000)

/* Memory Region Physical Addresses */
#define NVME_METADATA_PADDR (0x5FFF0000)
#define NVME_ASQ_PADDR (NVME_METADATA_PADDR + 0x0000)
#define NVME_ACQ_PADDR (NVME_METADATA_PADDR + 0x1000)
#define NVME_IO_SQ_PADDR (NVME_METADATA_PADDR + 0x2000)
#define NVME_IO_CQ_PADDR (NVME_METADATA_PADDR + 0x3000)
#define NVME_PRP_LIST_PADDR (NVME_METADATA_PADDR + 0x4000)
#define NVME_DATA_REGION_PADDR (0x5FDF0000)

#define NVME_IRQ 17

/* Map sDDF IDs to NVMe CIDs */
#define MAX_PENDING_REQS 1024
static uint32_t cid_to_id[MAX_PENDING_REQS];
static uint16_t cid_to_count[MAX_PENDING_REQS];

#define NVME_ASQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / sizeof(nvme_submission_queue_entry_t))
#define NVME_ACQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / sizeof(nvme_completion_queue_entry_t))
_Static_assert(NVME_ASQ_CAPACITY <= 0x1000, "capacity of ASQ must be <=4096 (entries)");
_Static_assert(NVME_ACQ_CAPACITY <= 0x1000, "capacity of ACQ must be <=4096 (entries)");
#define NVME_IO_SQ_CAPACITY (NVME_IO_QUEUE_SIZE / sizeof(nvme_submission_queue_entry_t))
#define NVME_IO_CQ_CAPACITY (NVME_IO_QUEUE_SIZE / sizeof(nvme_completion_queue_entry_t))
// §3.3.3.1
_Static_assert(NVME_IO_SQ_CAPACITY <= 0x10000, "capacity of IO SQ must be <=65536 (entries)");
_Static_assert(NVME_IO_CQ_CAPACITY <= 0x10000, "capacity of IO CQ must be <=65536 (entries)");

/* I/O Port Configuration */
#define PCI_CONFIG_ADDR_IOPORT_ID 1
#define PCI_CONFIG_DATA_IOPORT_ID 2
#define PCI_CONFIG_ADDR_PORT 0xCF8
#define PCI_CONFIG_DATA_PORT 0xCFC

static uint32_t pci_config_read_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset)
{
    uint32_t address = (uint32_t)((uint32_t)bus << 16) | ((uint32_t)dev << 11) | ((uint32_t)func << 8) | (offset & 0xfc)
                     | ((uint32_t)0x80000000);
    microkit_x86_ioport_write_32(PCI_CONFIG_ADDR_IOPORT_ID, PCI_CONFIG_ADDR_PORT, address);
    return microkit_x86_ioport_read_32(PCI_CONFIG_DATA_IOPORT_ID, PCI_CONFIG_DATA_PORT);
}

static void pci_config_write_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset, uint32_t value)
{
    uint32_t address = (uint32_t)((uint32_t)bus << 16) | ((uint32_t)dev << 11) | ((uint32_t)func << 8) | (offset & 0xfc)
                     | ((uint32_t)0x80000000);
    microkit_x86_ioport_write_32(PCI_CONFIG_ADDR_IOPORT_ID, PCI_CONFIG_ADDR_PORT, address);
    microkit_x86_ioport_write_32(PCI_CONFIG_DATA_IOPORT_ID, PCI_CONFIG_DATA_PORT, value);
}

void nvme_irq_mask(void)
{
    /* [NVMe-Transport-PCIe-1.1] 3.5.1.1 Differences between Pin Based and MSI Interrupts
        > Pin-based and single MSI only use one interrupt vector.
        > Multiple MSI may use up to 32 interrupt vectors.

       [NVme-2.1] 3.1.4.10 Admin Completion Queue Base Address
        > This queue is always associated with interrupt vector 0.
    */

    /* For now -- we mask out every interrupt vector) */
    nvme_controller->intms = 0xffffffff;
}

void nvme_irq_unmask(void)
{
    /* [NVMe-Transport-PCIe-1.1] 3.5.1.1 Differences between Pin Based and MSI Interrupts
        > Pin-based and single MSI only use one interrupt vector.
        > Multiple MSI may use up to 32 interrupt vectors.

       [NVme-2.1] 3.1.4.10 Admin Completion Queue Base Address
        > This queue is always associated with interrupt vector 0.
    */

    /* For now -- we mask in only vector 0, as it's the only one */
    nvme_controller->intmc = 0xffffffff;
}

static void handle_request(void)
{
    blk_req_code_t code;
    uintptr_t req_paddr;
    uint64_t block_number;
    uint16_t count;
    uint32_t id;

    while (blk_dequeue_req(&blk_queue, &code, &req_paddr, &block_number, &count, &id) == 0) {
        uint8_t opcode;

        if (code == BLK_REQ_READ) {
            opcode = 0x02;
        } else if (code == BLK_REQ_WRITE) {
            opcode = 0x01;
        } else {
            /* Support for FLUSH/BARRIER can be added here */
            int err = blk_enqueue_resp(&blk_queue, BLK_RESP_OK, 0, id);
            assert(!err);
            continue;
        }

        /* Translate sDDF 4096B blocks to NVMe 512B sectors. */
        uint64_t lba = block_number * 8;
        uint32_t nlb = (count * 8) - 1;

        /* Find a CID that isn't in use */
        static uint16_t next_cid = 0;
        uint16_t cid = next_cid;
        next_cid = (next_cid + 1) % MAX_PENDING_REQS;
        cid_to_id[cid] = id;
        cid_to_count[cid] = count;

        /*
         * PRP handling:
         * - PRP1 = first 4KB page
         * - PRP2 = second 4KB page (for 8KB transfer) or PRP list pointer (for >8KB)
         *
         * Note: req_paddr is the physical address of the client's data buffer.
         */
        uintptr_t data_paddr = req_paddr;
        uint64_t prp1 = data_paddr;
        uint64_t prp2 = 0;

        if (count == 2) {
            /* Simple case: 2 pages. PRP2 points directly to 2nd page. */
            prp2 = data_paddr + 0x1000;
        } else if (count > 2) {
            /* PRP2 points to a PRP List stored in the metadata region. */
            /* x86 hardcoded addresses */
            uint64_t *prp_list = (uint64_t *)(NVME_PRP_LIST_VADDR);
            uint64_t prp_list_paddr = NVME_PRP_LIST_PADDR;

            /* Fill the PRP List */
            for (int i = 1; i < count; i++) {
                prp_list[i - 1] = data_paddr + (i * 0x1000);
            }

            prp2 = prp_list_paddr;
        }

        nvme_queue_submit(&io_queue, &(nvme_submission_queue_entry_t) {
                                         .cdw0 = (cid << 16) | opcode,
                                         .nsid = 0x1,
                                         .cdw10 = (uint32_t)lba,
                                         .cdw11 = (uint32_t)(lba >> 32),
                                         .cdw12 = (1U << 31) | nlb, /* LR=1 (Limited Retry) */
                                         .prp1 = prp1,
                                         .prp2 = prp2,
                                     });
    }
}

static void handle_admin_completions(void)
{
    nvme_completion_queue_entry_t entry;

    if (nvme_queue_consume(&admin_queue, &entry) != 0) {
        LOG_NVME("handle_admin_completion: no completion available\n");
        return;
    }

    uint16_t status = (entry.phase_tag_and_status >> 1) & 0x7fff;
    if (status != 0) {
        sddf_dprintf("NVMe admin command failed with status 0x%x in state %d\n", status, state_ctx.state);
        return;
    }

    LOG_NVME("Admin completion in state %d\n", state_ctx.state);

    switch (state_ctx.state) {
    case NVME_STATE_WAIT_IDENTIFY: {
        LOG_NVME("Identify Controller completed\n");

        // 8. The host determines any I/O Command Set specific configuration information
        //    For now, we assume that the controller supports only the NVM Command Set.

        // 9. Determine the number of I/O Submission Queues and I/O Completion Queues
        //    supported using the Set Features command with the Number of Queues feature identifier.
        //    After determining the number of I/O Queues, the NVMe Transport specific interrupt registers
        //    (e.g., MSI and/or MSI-X registers) should be configured
        uint16_t io_queue_id = 1;
        assert(nvme_io_sq_region != 0x0);
        assert(nvme_io_cq_region != 0x0);
        assert(nvme_io_sq_region_paddr != 0x0);
        assert(nvme_io_cq_region_paddr != 0x0);
        nvme_queues_init(&io_queue, io_queue_id, nvme_controller, nvme_io_sq_region, NVME_IO_SQ_CAPACITY,
                         nvme_io_cq_region, NVME_IO_CQ_CAPACITY);

        // §3.3.1.1 Queue Setup & Initialization
        // => Configures the size of the I/O Submission Queues (CC.IOSQES) and I/O Completion Queues (CC.IOCQES)
        /* n.b. CQ/SQ entry sizes are specified as 2^n; i.e. 2^4 = 16 and 2^6 = 64. */
        nvme_controller->cc |= (4 << NVME_CC_IOCQES_SHIFT) | (6 << NVME_CC_IOSQES_SHIFT);

        // 10. Allocate the appropriate number of I/O Completion Queues [...]
        //     The I/O Completion Queues are allocated using the Create I/O Completion Queue command.
        // §5.2.1
        nvme_queue_submit(&admin_queue,
                          &(nvme_submission_queue_entry_t) {
                              .cdw0 = /* CID */ (0b1010 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x5,
                              .cdw10 = /* QSIZE */ ((NVME_IO_CQ_CAPACITY - 1U) << 16) | /* QID */ io_queue_id,
                              .cdw11 = /* IV */ (0x0 << 16) | /* IEN */ 1 << 1 | /* PC */ 0x1,
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
        uint16_t io_queue_id = 1;

        nvme_queue_submit(&admin_queue,
                          &(nvme_submission_queue_entry_t) {
                              .cdw0 = /* CID */ (0b1110 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x1,
                              .cdw10 = /* QSIZE */ ((NVME_IO_SQ_CAPACITY - 1U) << 16) | /* QID */ io_queue_id,
                              .cdw11 = /* CQID */ (io_queue_id << 16) | /* QPRIO */ (0b00 << 1) | /* PC */ 0b1,
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
        storage_info->capacity = 0x4000; /* 64MB / 4KB = 16384 blocks */
        storage_info->block_size = 4096;

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
        uint32_t id = cid_to_id[cid];
        uint16_t count = cid_to_count[cid];
        uint16_t status = (cq_entry.phase_tag_and_status >> 1) & 0x7fff;

        blk_resp_status_t resp_status = (status == 0) ? BLK_RESP_OK : BLK_RESP_ERR_UNSPEC;
        /* Return the original requested count on success */
        int err = blk_enqueue_resp(&blk_queue, resp_status, (resp_status == BLK_RESP_OK) ? count : 0, id);
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
                sddf_timer_set_timeout(timer_config.driver_id, 10 * NS_IN_MS);
                state_ctx.waited_ms += 10;
                return;
            }
            sddf_dprintf("NVMe reset timeout after %u ms\n", state_ctx.waited_ms);
            return;
        }
        LOG_NVME("controller reset complete\n");

        // 2. Configure Admin Queue(s); §3.5.1 steps 2-5
        nvme_queues_init(&admin_queue, /* y */ 0, nvme_controller, nvme_asq_region, NVME_ASQ_CAPACITY, nvme_acq_region,
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
        nvme_controller->cc |= 0b000 << NVME_CC_CSS_SHIFT;

        // 4a. Arbitration Mechanism
        // 4b. Memory Page Size
        int8_t cap_mps_max = (nvme_controller->cap >> 52) & 0xF;
        int8_t cap_mps_min = (nvme_controller->cap >> 48) & 0xF;

        // The maximum memory page size  is (2 ^ (12 + MPSMAX))
        assert(cap_mps_max >= 0);

        // The minimum memory page size is (2 ^ (12 + MPSMIN))
        assert(cap_mps_min <= 0);

        nvme_controller->cc &= ~NVME_CC_MPS_MASK;
        /* n.b. page size = 2 ^ (12 + MPS) */
        uint8_t page_size_log2 = 12; /* all architectures we care about have page size 2^12. */
        nvme_controller->cc |= ((page_size_log2 - 12) << NVME_CC_MPS_SHIFT) & NVME_CC_MPS_MASK;

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
                sddf_timer_set_timeout(timer_config.driver_id, 10 * NS_IN_MS);
                state_ctx.waited_ms += 10;
                return;
            }
            sddf_dprintf("NVMe enable timeout after %u ms\n", state_ctx.waited_ms);
            return;
        }
        LOG_NVME("controller ready\n");

        // 7. Send the Identify Controller command (Identify with CNS = 01h); §5.1.13
        // Unmask interrupts before submitting admin commands
        nvme_irq_unmask();

        nvme_queue_submit(&admin_queue,
                          &(nvme_submission_queue_entry_t) {
                              .cdw0 = /* CID */ (0b1111 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x6,
                              .cdw10 = /* CNTID[31:16] */ 0x0 | /* CNS */ 0x01,
                              .prp2 = 0,
                              .prp1 = NVME_DATA_REGION_PADDR, /* Data region for identify - hardcoded for x86 */
                          });

        state_ctx.state = NVME_STATE_WAIT_IDENTIFY;
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
    uint32_t vs = nvme_controller->vs;
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
    uint8_t cap_to = (nvme_controller->cap >> 24) & 0xFF;

    // Initialize state machine context
    state_ctx = (nvme_state_ctx_t) {
        .state = NVME_STATE_WAIT_NOT_READY,
        .timeout_ms = (cap_to + 1) * 500,
        .waited_ms = 0,
    };

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
    uint32_t vid_did = pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, 0x00);
    LOG_NVME("VendorID:DeviceID = %08x\n", vid_did);

    uint32_t bar0 = pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, 0x10);
    LOG_NVME("NVMe PCI BAR0 readback: %08x\n", bar0);

    /* Enable Bus Master and Memory Space */
    uint32_t cmd = pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, 0x04);
    pci_config_write_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, 0x04, cmd | 0x6);
    LOG_NVME("PCI Command Register: %08x\n", pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, 0x04));

    /* Check Interrupt Configuration */
    uint32_t intr_info = pci_config_read_32(NVME_PCI_BUS, NVME_PCI_DEV, NVME_PCI_FUNC, 0x3C);
    uint8_t intr_line = intr_info & 0xFF;
    uint8_t intr_pin = (intr_info >> 8) & 0xFF;
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

    /* NVMe Controller Init */
    nvme_controller_init();
}

void notified(microkit_channel ch)
{
    if (ch == NVME_IRQ) { /* NVMe IRQ - hardcoded for x86 */
        handle_irq();
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
