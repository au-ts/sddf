#pragma once

#include <stdint.h>
#include <stddef.h>

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
#define NVME_CAP_NOIOCSS BIT(37 + 7) /* No I/O Command Set Support */
#define NVME_CAP_IOCSS   BIT(37 + 6) /* I/O Command Set Support    */
#define NVME_CAP_NCSS    BIT(37 + 0) /* NVM Command Set Support    */

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
