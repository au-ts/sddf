#include "nvme.h"
#include "nvme_queue.h"

#include <sddf/util/printf.h>

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

uintptr_t data_region_paddr;
volatile uint8_t *data_region;

/* TODO: don't hardcode 64? is 64 even right for CQ?? */
#define NVME_ASQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / 64)
#define NVME_ACQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / 64)
_Static_assert(NVME_ASQ_CAPACITY <= 0x1000, "capacity of ASQ must be <=4096 (entries)");
_Static_assert(NVME_ACQ_CAPACITY <= 0x1000, "capacity of ACQ must be <=4096 (entries)");
#define NVME_IOQ_CAPACITY (NVME_IO_QUEUE_SIZE / 64)
// §3.3.3.1
_Static_assert(NVME_ASQ_CAPACITY <= 0x10000, "capacity of ASQ must be <=65536 (slots)");

static void nvme_debug_dump_controller_regs()
{
    sddf_dprintf("CAP: %016lx\n", nvme_controller->cap);
    sddf_dprintf("VS: major: %u, minor: %u, tertiary: %u\n", nvme_controller->vs.mjr, nvme_controller->vs.mnr,
                 nvme_controller->vs.ter);
    sddf_dprintf("INTMS: %08x\n", nvme_controller->intms);
    sddf_dprintf("INTMC: %08x\n", nvme_controller->intmc);
    sddf_dprintf("CC: %08x\n", nvme_controller->cc);
    sddf_dprintf("CSTS: %08x\n", nvme_controller->csts);
    sddf_dprintf("AQA: %08x\n", nvme_controller->aqa);
    sddf_dprintf("ASQ: %016lx\n", nvme_controller->asq);
    sddf_dprintf("ACQ: %016lx\n", nvme_controller->acq);
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
            sddf_dprintf("received a response for submission with CDW0: %x\n", entry->cdw0);
            return response;
        }

        if (i % 100 == 0) {
            sddf_dprintf("waiting for response to submission with CDW0: %x\n", entry->cdw0);
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

/* [NVMe-2.1] 3.5.1 Memory-based Controller Initialization (PCIe) */
void nvme_controller_init()
{
    sddf_dprintf("CAP: %016lx\n", nvme_controller->cap);
    sddf_dprintf("VS: major: %u, minor: %u, tertiary: %u\n", nvme_controller->vs.mjr, nvme_controller->vs.mnr,
                 nvme_controller->vs.ter);
    sddf_dprintf("CC: %08x\n", nvme_controller->cc);


    nvme_controller->cc &= ~NVME_CC_EN;

    // 1. Wait for CSTS.RDY to become '0' (i.e. not ready)
    while (nvme_controller->csts & NVME_CSTS_RDY);

    // 2. Configure Admin Queue(s); i.e. y = 0.
    nvme_queues_init(&admin_queue, 0, nvme_controller, nvme_asq_region, nvme_acq_region, NVME_ASQ_CAPACITY); // todo: capacity?
    assert(nvme_asq_region_paddr != 0x0);
    assert(nvme_acq_region_paddr != 0x0);
    nvme_controller->asq = nvme_asq_region_paddr;
    nvme_controller->acq = nvme_acq_region_paddr;
    nvme_controller->aqa &= ~(NVME_AQA_ACQS_MASK | NVME_AQA_ASQS_MASK);
    nvme_controller->aqa |= ((NVME_ASQ_CAPACITY - 1) << NVME_AQA_ASQS_SHIFT)
                          | ((NVME_ACQ_CAPACITY - 1) << NVME_AQA_ACQS_SHIFT);

    // 3. Initialise Command Support Sets.
    nvme_controller->cc &= ~(NVME_CC_CSS_MASK);
    if (nvme_controller->cap & NVME_CAP_NOIOCSS) {
        nvme_controller->cc |= 0b111 << NVME_CC_CSS_SHIFT;
    } else if (nvme_controller->cap & NVME_CAP_IOCSS) {
        nvme_controller->cc |= 0b110 << NVME_CC_CSS_SHIFT;
    } else if (nvme_controller->cap & NVME_CAP_NCSS) {
        nvme_controller->cc |= 0b000 << NVME_CC_CSS_SHIFT;
    }

    // 4a. Arbitration Mechanism (TODO)
    // 4b. Memory Page Size
    // TODO: Check CAP.MPSMAX/CAP.MPSMIN fields
    nvme_controller->cc &= ~NVME_CC_MPS_MASK;
    /* n.b. page size = 2 ^ (12 + MPS) */
    uint8_t page_size_log2 = 12; /* all architectures we care about have page size 2^12. */
    nvme_controller->cc |= ((page_size_log2 - 12) << NVME_CC_MPS_SHIFT) & NVME_CC_MPS_MASK;

    // TODO: See initialisation note under §4.2.4; fine since already that way.

    // 5. Enable the controller
    nvme_controller->cc |= NVME_CC_EN;

    // 6. Wait for ready
    sddf_dprintf("waiting ready...\n");
    while (!(nvme_controller->csts & NVME_CSTS_RDY));
    sddf_dprintf("\tdone\n");

    // 7. Send the Identify Controller command (Identify with CNS = 01h); §5.1.13
    // TODO: What do we actually need this for????
    // sudo nvme admin-passthru /dev/nvme0 --opcode=0x06 --cdw10=0x0001 --data-len=4096 -r  -s
    nvme_completion_queue_entry_t entry;
    entry = nvme_queue_submit_and_consume_poll(&admin_queue, &(nvme_submission_queue_entry_t){
        .cdw0 = /* CID */ (0b1111 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x6,
        .cdw10 = /* CNTID[31:16] */ 0x0 | /* CNS */ 0x01,
        .dptr_hi = 0,
        .dptr_lo = data_region_paddr, /* TEMP */
    });

    assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

    // 8. The host determines any I/O Command Set specific configuration information
    // TODO: Why???

    // 9. Determine the number of I/O Submission Queues and I/O Completion Queues
    //    supported using the Set Features command with the Number of Queues feature identifier.
    //    After determining the number of I/O Queues, the NVMe Transport specific interrupt registers
    //    (e.g., MSI and/or MSI-X registers) should be configured
    // TODO: interrupts. & don't ignore # but we always use one, so.
    uint16_t io_queue_id = 1;
    assert(nvme_io_sq_region != 0x0);
    assert(nvme_io_cq_region != 0x0);
    assert(nvme_io_sq_region_paddr != 0x0);
    assert(nvme_io_cq_region_paddr != 0x0);
    nvme_queues_init(&io_queue, io_queue_id, nvme_controller, nvme_io_sq_region, nvme_io_cq_region, NVME_IOQ_CAPACITY); // todo: capacity?

    // §3.3.1.1 Queue Seutp & Initialization
        // => Configures the size of the I/O Submission Queues (CC.IOSQES) and I/O Completion Queues (CC.IOCQES)
    // nvme_controller->cc &= ~(NVME_CC_IOCQES_MASK | NVME_CC_IOSQES_MASK);
    /* n.b. CQ/SQ entry sizes are specified as 2^n; i.e. 2^4 = 16 and 2^6 = 64. */
    nvme_controller->cc |= (4 << NVME_CC_IOCQES_SHIFT) | (6 << NVME_CC_IOSQES_SHIFT);

    // 10. Allocate the appropriate number of I/O Completion Queues [...]
    //     The I/O Completion Queues are allocated using the Create I/O Completion Queue command.
    // §5.2.1
    entry = nvme_queue_submit_and_consume_poll(&admin_queue, &(nvme_submission_queue_entry_t){
        .cdw0 = /* CID */ (0b1010 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x5,
        .cdw10 = /* QSIZE */ ((NVME_IOQ_CAPACITY - 1)<< 16) | /* QID */ io_queue_id,
        .cdw11 = /* IV */ (0x0 << 16) | /* IEN */ 0 << 1 | /* PC */ 0x1,
        .dptr_hi = 0,
        .dptr_lo = nvme_io_cq_region_paddr,
    });

    assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

    // 11. Allocate the appropriate number of I/O Submission Queues [...]
    //     The I/O Submission Queues are allocated using the Create I/O Submission Queue command.
    // §5.2.2
    entry = nvme_queue_submit_and_consume_poll(&admin_queue, &(nvme_submission_queue_entry_t){
        .cdw0 = /* CID */ (0b1110 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x1,
        .cdw10 = /* QSIZE */ ((NVME_IOQ_CAPACITY-1) << 16) | /* QID */ io_queue_id,
        .cdw11 = /* CQID */ (io_queue_id << 16) | /* QPRIO */ (0b00 << 1) | /* PC */ 0b1,
        .cdw12 = 0,
        .dptr_hi = 0,
        .dptr_lo = nvme_io_sq_region_paddr,
    });

    sddf_dprintf("CDW0: %04x\n", entry.cdw0);
    sddf_dprintf("CDW1: %04x\n", entry.cdw1);
    sddf_dprintf("SQHD: %02x\n", entry.sqhd);
    sddf_dprintf("SQID: %02x\n", entry.sqid);
    sddf_dprintf(" CID: %02x\n", entry.cid);
    sddf_dprintf("P&STATUS: %02x\n", entry.phase_tag_and_status);
    // should exist again.
    assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field
    return;

    // try a get log page command (0x2)
    sddf_dprintf("!!! LOG PAGE !!!\n");
    entry = nvme_queue_submit_and_consume_poll(&admin_queue, &(nvme_submission_queue_entry_t){
        .cdw0 = /* CID */ (0b1001 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x2,
        .dptr_hi = 0,
        .dptr_lo = data_region_paddr,
        .cdw10 = /* NUMDL*/ (0x100 << 16) | /* LID*/ 0x01,
        .cdw11 = 0x0,
        .cdw12 = 0x0,
    });

    assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

    volatile nvme_error_information_log_page_t *errors = (volatile void*)data_region;
    for (int i = 0; i < 2; i++) {
        sddf_dprintf("Error 0x%lx\n", errors[i].ecnt);
        // These produce Store/AMO faults, NEAR THE BEGINNING of this function??? TODO???
        // sddf_dprintf("\tSQID: 0x%x\n", errors[i].sqid);
        // sddf_dprintf("\t CID: 0x%x\n", errors[i].cid);
        sddf_dprintf("\t STS: 0x%x\n", errors[i].sts);
        sddf_dprintf("\t PEL: 0x%x\n", errors[i].pel);
        sddf_dprintf("\t(elided)\n");
    }
}

void nvme_init()
{
    sddf_dprintf("Starting NVME config...\n");

    // We should do a Function Level Reset as defined by [PCIe-2.0] spec §6.6.2

    // https://github.com/bootreer/vroom/blob/d8bbe9db2b1cfdfc38eec31f3b48f5eb167879a9/src/nvme.rs#L220

    nvme_controller_init();
}
