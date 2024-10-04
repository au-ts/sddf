#pragma once

#include <stdint.h>
#include <stddef.h>

#include <sddf/util/util.h>

/*
    References:

    [NVMe-2.1] NVM Express Base Specification Revision 2.1 (Aug 5, 2024)
        https://nvmexpress.org/wp-content/uploads/NVM-Express-Base-Specification-Revision-2.1-2024.08.05-Ratified.pdf

    [NVMEe-Transport-PCIe-1.1] NVMe over PCIe Transport Specification, Revision 1.1 (Aug 5, 2024)
        https://nvmexpress.org/wp-content/uploads/NVM-Express-PCI-Express-Transport-Specification-Revision-1.1-2024.08.05-Ratified.pdf
*/

/* [NVMe-2.1] Section 3.1.4 Controller Properties
    RO = Read Only
    RW = Read Write
    RWC = Read/Write '1' to clear
    RWS = Read/Write '1' to set
*/
typedef struct nvme_controller {
    uint64_t cap;     /* Controller Capabilities (RO) */
    struct vs {
        uint8_t ter;  /* Tertiary Version */
        uint8_t mnr;  /* Minor Version */
        uint16_t mjr; /* Major Version */
    } vs;             /* Version (RO) */
    uint32_t intms;   /* Interrupt Mask Set (RWS) */
    uint32_t intmc;   /* Interrupt Mask Clear (RWC) */
    uint32_t cc;      /* Controller Configuration (RW) */
    uint32_t _reserved;
    uint32_t csts;    /* Controller Status */
    uint32_t nssr;    /* NVM Subsystem Reset (optional) */
    uint32_t aqa;     /* Admin Queue Attributes */
    uint64_t asq;     /* Admin Submission Queue Base Address */
    uint64_t acq;     /* Admin Completion Queue Base Address */

    uint32_t cmbloc;  /* Controller Memory Buffer Location (optional) */
    uint32_t cmbsz;   /* Controller Memory Buffer Size (optional) */
    uint32_t bpinfo;  /* Boot Partition Information (optional) */
    uint32_t bprsel;  /* Boot Partition Read Select (optional) */
    uint64_t bpmbl;   /* Boot Partition Memory Buffer Location (optional) */
    uint64_t cmbmsc;  /* Controller Memory Buffer Memory Space Control (optional) */
    uint32_t cmbsts;  /* Controller Memory Buffer Status (optional) */
    uint32_t cmbebs;  /* Controller Memory Buffer Elasticity Buffer Size (optional) */
    uint32_t cmbswtp; /* Controller Memory Buffer Sustained Write Throughput (optional) */
    uint32_t nssd;    /* NVM Subsystem Shutdown (optional) */

    uint32_t crto;    /* Controller Ready Timeouts */
    uint32_t _reserved2;
} nvme_controller_t;

_Static_assert(offsetof(nvme_controller_t, _reserved2) == 0x6C, "nvme_controller_t must match spec layout");

#define _LEN(start, end) ((end - start) + 1)
#define _MASK(start, end)  ((BIT(_LEN(start, end)) - 1) << (start))

/* [NVMe-2.1] 3.1.4.1 Offset 0h: CAP – Controller Capabilities */
#define NVME_CAP_NOIOCSS     BIT(37 + 7)   /* No I/O Command Set Support */
#define NVME_CAP_IOCSS       BIT(37 + 6)   /* I/O Command Set Support    */
#define NVME_CAP_NCSS        BIT(37 + 0)   /* NVM Command Set Support    */
#define NVME_CAP_DSTRD_SHIFT 32            /* Doorbell Stride (2 ^ (2 + DSTRD)) */
#define NVME_CAP_DSTRD_MASK  _MASK(32, 35) /* Doorbell Stride (2 ^ (2 + DSTRD)) */

/* [NVMe-2.1] 3.1.4.5 Offset 14h: CC – Controller Configuration */
#define NVME_CC_MPS_SHIFT 7            /* Host Memory Page Size */
#define NVME_CC_MPS_MASK  _MASK(7, 10) /* Host Memory Page Size */
#define NVME_CC_CSS_SHIFT 4            /* I/O Command Set Selected */
#define NVME_CC_CSS_MASK  _MASK(4, 6)  /* I/O Command Set Selected */
#define NVME_CC_EN        BIT(0)       /* Controller Enable */

/* [NVMe-2.1] 3.1.4.6 Offset 1Ch: CSTS – Controller Status */
#define NVME_CSTS_RDY BIT(0) /* Controller Ready (RO) */

/* [NVMe-2.1] 3.1.4.7 Offset 20h: NSSR – NVM Subsystem Reset */
#define NVME_NSSRC_VALUE (0x4E564D65) /* NVM Subsystem Reset Control - Reset value */

/* [NVMe-2.1] 3.1.4.8 Offset 24h: AQA – Admin Queue Attributes */
#define NVME_AQA_ACQS_SHIFT 16             /* Admin Completion Queue Size (#entries) */
#define NVME_AQA_ACQS_MASK  _MASK(16, 27)  /* Admin Completion Queue Size (#entries) */
#define NVME_AQA_ASQS_SHIFT 0              /* Admin Submission Queue Size (#entries) */
#define NVME_AQA_ASQS_MASK  _MASK(0, 11)   /* Admin Submission Queue Size (#entries) */

/**
 * Queue Structures
 */

/* [NVMe-2.1] 4.1 Submission Queue Entry */
typedef struct nvme_submission_queue_entry {
    // TODO: split out to opcode etc (figure 91??)

    uint32_t cdw0; /* Command Dword 0 (common) */
    uint32_t nsid; /* Namespace Identifier */
    uint32_t cdw2; /* Command Dword 2 (command-specific) */
    uint32_t cdw3; /* Command Dword 3 (command-specific) */
    uint64_t mptr; /* Metadata Pointer */
    uint64_t dptr_lo; /* Data Pointer (low 8 bytes)  */
    uint64_t dptr_hi; /* Data Pointer (high 8 bytes) */
    uint32_t cdw10; /* Command Dword 10 (command-specific) */
    uint32_t cdw11; /* Command Dword 11 (command-specific) */
    uint32_t cdw12; /* Command Dword 12 (command-specific) */
    uint32_t cdw13; /* Command Dword 13 (command-specific) */
    uint32_t cdw14; /* Command Dword 14 (command-specific) */
    uint32_t cdw15; /* Command Dword 15 (command-specific) */
} nvme_submission_queue_entry_t;
_Static_assert(sizeof(nvme_submission_queue_entry_t) == 64, "Each Common Command Format command is 64 bytes in size.");

/* [NVMe-2.1] 4.2 Completion Queue Entry */
typedef struct nvme_completion_queue_entry {
    uint32_t cdw0; /* Command Dword 0 (command-specific) */
    uint32_t cdw1; /* Command Dword 1 (command-specific) */
    uint16_t sqhd; /* Submission Queue Head Pointer */
    uint16_t sqid; /* Submission Queue ID */
    uint16_t cid;  /* Command Identifier */
    uint16_t phase_tag_and_status; /* Phase Tag (P) and Status */
} nvme_completion_queue_entry_t;
_Static_assert(sizeof(nvme_completion_queue_entry_t) == 16,
               "The Common Completion Queue Entry Layout is 16 bytes in size");

/**
 * Below here is NVMe PCIe Transport Specific Properties.
 */

#define NVME_PCIE_SQT_MASK _MASK(0, 15) /* Submission Queue Tail*/
#define NVME_PCIE_CQH_MASK _MASK(0, 15) /* Completion Queue Head */

#define NVME_PCIE_DOORBELL_OFFSET(i, DSTRD) (0x1000 + ((i) * (4 << (DSTRD))))
