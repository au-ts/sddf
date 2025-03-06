#include <sddf/util/printf.h>

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

void nvme_irq_mask(void)
{
    /* [NVMe-Transport-PCIe-1.1] 3.5.1.1 Differences between Pin Based and MSI Interrupts
        > Pin-based and single MSI only use one interrupt vector.
        > Multiple MSI may use up to 32 interrupt vectors.

       [NVMe-2.1] 3.1.4.10 Admin Completion Queue Base Address
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

       [NVMe-2.1] 3.1.4.10 Admin Completion Queue Base Address
        > This queue is always associated with interrupt vector 0.
    */

    /* For now -- we mask in only vector 0, as it's the only one */
    nvme_controller->intmc = 0xffffffff;
}

/* [NVMe-2.1] 3.5.1 Memory-based Controller Initialization (PCIe) */
void nvme_controller_init()
{
    LOG_NVME("CAP: %016lx\n", nvme_controller->cap);
    // TODO: alignment 32-bit.
    // LOG_NVME("VS: major: %u, minor: %u, tertiary: %u\n", nvme_controller->vs.mjr, nvme_controller->vs.mnr,
            //  nvme_controller->vs.ter);
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
    nvme_irq_mask();
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

#if defined(CONFIG_PLAT_QEMU_RISCV_VIRT) || defined(CONFIG_PLAT_QEMU_ARM_VIRT)
    /*
        QEMU deviates from the NVMe specification:
        https://gitlab.com/qemu-project/qemu/-/issues/1691
    */
   nvme_controller->cc &= ~(NVME_CC_CSS_MASK);
   nvme_controller->cc |= 0b000 << NVME_CC_CSS_SHIFT;
#endif

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
        .cdw11 = /* IV */ (0x0 << 16) | /* IEN */ 1 << 1 | /* PC */ 0x1,
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

    nvme_irq_unmask();
}

void nvme_continue(int z);
void nvme_init()
{
    LOG_NVME("Starting NVME initialisation... (%s)\n", microkit_name);

    // We should do a Function Level Reset as defined by [PCIe-2.0] spec §6.6.2

    // https://github.com/bootreer/vroom/blob/d8bbe9db2b1cfdfc38eec31f3b48f5eb167879a9/src/nvme.rs#L220

    nvme_controller_init();
    LOG_NVME("NVME initialised\n");

    /* TODO: Don't send via this */
    nvme_continue(0);
}

#define NUMBER_BLOCKS 1
void nvme_continue(int z)
{
    if (z == 0) {
        /* [NVMe-CommandSet-1.1] 3.3.4 Read command */
        nvme_queue_submit(&io_queue, &(nvme_submission_queue_entry_t){
            .cdw0 = /* CID */ (0b1011 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x2,
            .nsid = 0x1, // TOOD: Why is NSID 1 now ????
            .cdw10 = /* SLBA[31:00] */ 0x0,
            .cdw11 = /* SLBA[63:32] */ 0x0,
            .cdw12 = /* LR */ (0b1U << 31) | /* others */ 0 | /* NLB */ (NUMBER_BLOCKS - 1),
            .prp2 = 0x0,
            .prp1 = data_region_paddr,
        });
    } else if (z == 1) {
        sddf_dprintf("doing nothing :P -- should get another IRQ \n");
        /*
            So this works fine on QEMU AArch64...
            but on QEMU RISCV level interrupts only get triggerred once
            ... this caused issues in linux
            ... https://www.mail-archive.com/qemu-devel@nongnu.org/msg931360.html
        */
    } else if (z == 2) {
        nvme_completion_queue_entry_t cq_entry;
        int ret = nvme_queue_consume(&io_queue, &cq_entry);
        assert(ret == 0);
        assert((cq_entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

        for (int i = 0; i < 8; i++) {
            LOG_NVME("Data [%02x]: %02x\n", i, data_region[i]);
        }

        for (int i = 0; i < 4096; i++) {
            data_region[i] = data_region[i] ^ 0xbb;
        }

        /* [NVMe-CommandSet-1.1] ??????? write */
        nvme_queue_submit(&io_queue, &(nvme_submission_queue_entry_t){
            .cdw0 = /* CID */ (0b1101 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x1,
            .nsid = 0x1, // TOOD: Why is NSID 1 now ????
            .cdw10 = /* SLBA[31:00] */ 0x0,
            .cdw11 = /* SLBA[63:32] */ 0x0,
            .cdw12 = /* LR */ (0b1U << 31) | /* others */ 0 | /* NLB */ (NUMBER_BLOCKS - 1),
            .prp2 = 0x0,
            .prp1 = data_region_paddr,
        });
    } else if (z == 3) {
        nvme_completion_queue_entry_t cq_entry;
        int ret = nvme_queue_consume(&io_queue, &cq_entry);
        assert(ret == 0);
        assert((cq_entry.phase_tag_and_status & _MASK(1, 15)) == 0x0); // §4.2.3 Status Field

        LOG_NVME("Got response for write!\n");
    }
}
