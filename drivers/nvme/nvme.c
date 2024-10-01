#include "nvme.h"
#include "nvme_queue.h"

#include <sddf/util/printf.h>

volatile nvme_controller_t *nvme_controller;
volatile nvme_submission_queue_entry_t *nvme_asq_region;
volatile nvme_completion_queue_entry_t *nvme_acq_region;
uintptr_t nvme_asq_region_paddr;
uintptr_t nvme_acq_region_paddr;
#define NVME_ADMIN_QUEUE_SIZE 0x1000


uintptr_t data_region_paddr;
uint8_t *data_region;

/* TODO: don't hardcode */
#define NVME_ASQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / 64)
#define NVME_ACQ_CAPACITY (NVME_ADMIN_QUEUE_SIZE / 64)
_Static_assert(NVME_ASQ_CAPACITY <= 0x1000, "capacity of ASQ must be <=4096 (entries)");
_Static_assert(NVME_ACQ_CAPACITY <= 0x1000, "capacity of ACQ must be <=4096 (entries)");

/* [NVMe-2.1] 3.3.1 Memory-based Transport Queue Model (PCIe) */
void nvme_queue_init()
{
    // TODO.
}

void nvme_debug_dump_controller_regs()
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

    // 2. Configure Admin Queue(s)
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
    nvme_controller->cc &= ~NVME_CC_MPS_MASK;
    /* n.b. page size = 2 ^ (12 + MPS) */
    nvme_controller->cc |= ((PAGE_SIZE >> 12) << NVME_CC_MPS_SHIFT) & NVME_CC_MPS_MASK;

    // TODO: See initialisation note under §4.2.4; fine since already that way.

    // 5. Enable the controller
    nvme_controller->cc |= NVME_CC_EN;

    // 6. Wait for ready
    sddf_dprintf("waiting ready...\n");
    while (!(nvme_controller->csts & NVME_CSTS_RDY));
    sddf_dprintf("\tdone\n");

    // 7. Send the Identify Controller command (Identify with CNS = 01h)
    uint8_t DSTRD = (nvme_controller->cap & NVME_CAP_DSTRD_MASK) >> NVME_CAP_DSTRD_SHIFT;

    // Identify Command (5.1.13)
    nvme_queue_submit(nvme_asq_region, nvme_controller, DSTRD, &(nvme_submission_queue_entry_t){
        .cdw0 = /* CID */ (0b1111 << 16) | /* PSDT */ 0 | /* FUSE */ 0 | /* OPC */ 0x6,
        .cdw10 = /* CNTID[31:16] */ 0x0 | /* CNS */ 0x01,
        .dptr_hi = 0,
        .dptr_lo = data_region_paddr, /* TEMP */
    });

    nvme_completion_queue_entry_t entry;
    while (true) {
        int ret = nvme_queue_consume(nvme_acq_region, nvme_controller, DSTRD, &entry);
        if (ret == 0) {
            sddf_dprintf("succeed\n");
            /* succeeded */
            break;
        }
        sddf_dprintf("fail\n");
    }

    sddf_dprintf("CDW0: %04x\n", entry.cdw0);
    sddf_dprintf("CDW1: %04x\n", entry.cdw1);
    sddf_dprintf("SQHD: %02x\n", entry.sqhd);
    sddf_dprintf("SQID: %02x\n", entry.sqid);
    sddf_dprintf(" CID: %02x\n", entry.cid);
    sddf_dprintf("P&STATUS: %02x\n", entry.phase_tag_and_status);

    // sudo nvme admin-passthru /dev/nvme0 --opcode=0x06 --cdw10=0x0001 --data-len=4096 -r  -s
    for (int i = 0; i < 64; i++) {
        sddf_dprintf("[%04x]: %x: %c\n", i, data_region[i], data_region[i]);
    }
}

void nvme_init()
{
    sddf_dprintf("Starting NVME config...\n");

    // We should do a Function Level Reset as defined by [PCIe-2.0] spec §6.6.2

    // https://github.com/bootreer/vroom/blob/d8bbe9db2b1cfdfc38eec31f3b48f5eb167879a9/src/nvme.rs#L220

    nvme_controller_init();
    nvme_queue_init();
}
