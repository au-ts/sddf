#include <sddf/util/printf.h>

#include "nvme.h"
#include "nvme_queue.h"

#define DEBUG_DRIVER
#ifdef DEBUG_DRIVER
#include "nvme_debug.h"
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

uintptr_t data_region_paddr;
volatile uint8_t *data_region;

#define NVME_ASQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / sizeof(nvme_submission_queue_entry_t))
#define NVME_ACQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / sizeof(nvme_completion_queue_entry_t))
_Static_assert(NVME_ASQ_CAPACITY <= 0x1000, "capacity of ASQ must be <=4096 (entries)");
_Static_assert(NVME_ACQ_CAPACITY <= 0x1000, "capacity of ACQ must be <=4096 (entries)");
#define NVME_IO_SQ_CAPACITY (NVME_IO_QUEUE_SIZE / sizeof(nvme_submission_queue_entry_t))
#define NVME_IO_CQ_CAPACITY (NVME_IO_QUEUE_SIZE / sizeof(nvme_completion_queue_entry_t))
// §3.3.3.1
_Static_assert(NVME_IO_SQ_CAPACITY <= 0x10000, "capacity of IO SQ must be <=65536 (entries)");
_Static_assert(NVME_IO_CQ_CAPACITY <= 0x10000, "capacity of IO CQ must be <=65536 (entries)");

/* [NVMe-2.1] 3.5.1 Memory-based Controller Initialization (PCIe) */
void nvme_controller_init()
{
    LOG_NVME("CAP: %016lx\n", nvme_controller->cap);
    LOG_NVME("VS: major: %u, minor: %u, tertiary: %u\n", nvme_controller->vs.mjr, nvme_controller->vs.mnr,
             nvme_controller->vs.ter);
    LOG_NVME("CC: %08x\n", nvme_controller->cc);

    nvme_controller->cc &= ~NVME_CC_EN;

    // 1. Wait for CSTS.RDY to become '0' (i.e. not ready)
    int i = 100;
    while (nvme_controller->csts & NVME_CSTS_RDY && i != 0) i--;
    if (i == 0) {
        sddf_dprintf("time out\n");
        return;
    }

    // 2. Configure Admin Queue(s);
    nvme_queues_init(&admin_queue, /* y */ 0, nvme_controller, nvme_asq_region, NVME_ASQ_CAPACITY, nvme_acq_region,
                     NVME_ACQ_CAPACITY);
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
    LOG_NVME("waiting ready...\n");
    while (!(nvme_controller->csts & NVME_CSTS_RDY));
    LOG_NVME("\tdone\n");

    /* https://github.com/redox-os/drivers/blob/master/storage/nvmed/src/nvme/mod.rs#L292*/
    nvme_controller->intms = 0xFFFFFFFF;
    nvme_controller->intmc = 0x00000001;

    // 7. Send the Identify Controller command (Identify with CNS = 01h); §5.1.13
    // TODO: What do we actually need this for????
    // sudo nvme admin-passthru /dev/nvme0 --opcode=0x06 --cdw10=0x0001 --data-len=4096 -r  -s
    nvme_completion_queue_entry_t entry;
    entry = nvme_queue_submit_and_consume_poll(&admin_queue, &(nvme_submission_queue_entry_t){
        .cdw0 = /* CID */ (0b1111 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x6,
        .cdw10 = /* CNTID[31:16] */ 0x0 | /* CNS */ 0x01,
        .prp2 = 0,
        .prp1 = data_region_paddr, /* TEMP */
    });

    assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

    nvme_controller->intms = 0x00000001;
    /* At this point: we start getting interrupts */
    return;

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
    nvme_queues_init(&io_queue, io_queue_id, nvme_controller, nvme_io_sq_region, NVME_IO_SQ_CAPACITY, nvme_io_cq_region,
                     NVME_IO_CQ_CAPACITY);

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
        .cdw10 = /* QSIZE */ ((NVME_IO_CQ_CAPACITY - 1U) << 16) | /* QID */ io_queue_id,
        .cdw11 = /* IV */ (0x0 << 16) | /* IEN */ 0 << 1 | /* PC */ 0x1,
        .prp2 = 0,
        .prp1 = nvme_io_cq_region_paddr,
    });

    assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

    // 11. Allocate the appropriate number of I/O Submission Queues [...]
    //     The I/O Submission Queues are allocated using the Create I/O Submission Queue command.
    // §5.2.2
    entry = nvme_queue_submit_and_consume_poll(&admin_queue, &(nvme_submission_queue_entry_t){
        .cdw0 = /* CID */ (0b1110 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x1,
        .cdw10 = /* QSIZE */ ((NVME_IO_SQ_CAPACITY - 1U) << 16) | /* QID */ io_queue_id,
        .cdw11 = /* CQID */ (io_queue_id << 16) | /* QPRIO */ (0b00 << 1) | /* PC */ 0b1,
        .cdw12 = 0,
        .prp2 = 0,
        .prp1 = nvme_io_sq_region_paddr,
    });

    assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

    // 12. To enable asynchronous notification of optional events, the host should issue a Set Features
    // command specifying the events to enable. To enable asynchronous notification of events, the host
    // should submit an appropriate number of Asynchronous Event Request commands. This step may
    // be done at any point after the controller signals that the controller is ready (i.e., CSTS.RDY is set to ‘1’).
    // TODO: ???
}

void nvme_init()
{
    LOG_NVME("Starting NVME config... (%s)\n", microkit_name);

    // We should do a Function Level Reset as defined by [PCIe-2.0] spec §6.6.2

    // https://github.com/bootreer/vroom/blob/d8bbe9db2b1cfdfc38eec31f3b48f5eb167879a9/src/nvme.rs#L220

    nvme_controller_init();
    return;

    for (int z = 0; z < 9; z++) {
        /* [NVMe-CommandSet-1.1] 3.3.4 Read command */
        nvme_completion_queue_entry_t entry;
        uint16_t number_blocks = 1;
        entry = nvme_queue_submit_and_consume_poll(&io_queue, &(nvme_submission_queue_entry_t){
            .cdw0 = /* CID */ (0b1011 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x2,
            .nsid = 0x1, // TOOD: Why is NSID 1 now ????
            .cdw10 = /* SLBA[31:00] */ 0x0,
            .cdw11 = /* SLBA[63:32] */ 0x0,
            .cdw12 = /* LR */ (0b1U << 31) | /* others */ 0 | /* NLB */ (number_blocks - 1),
            .prp2 = 0x0,
            .prp1 = data_region_paddr,
        });

        assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

        // for (int i = 0; i < 32; i++) {
        //     sddf_dprintf("Data [%02x]: %02x\n", i, data_region[i]);
        // }

        for (int i = 0; i < 4096; i++) {
            data_region[i] = data_region[i] ^ 0xbb;
        }

        entry = nvme_queue_submit_and_consume_poll(&io_queue, &(nvme_submission_queue_entry_t){
            .cdw0 = /* CID */ (0b1101 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x1,
            .nsid = 0x1, // TOOD: Why is NSID 1 now ????
            .cdw10 = /* SLBA[31:00] */ 0x0,
            .cdw11 = /* SLBA[63:32] */ 0x0,
            .cdw12 = /* LR */ (0b1U << 31) | /* others */ 0 | /* NLB */ (number_blocks - 1),
            .prp2 = 0x0,
            .prp1 = data_region_paddr,
        });

        assert((entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

    }
}
