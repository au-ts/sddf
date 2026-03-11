/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <microkit.h>
#include <sddf/util/util.h>

/*
    References:

    [NVMe-2.1] NVM Express Base Specification Revision 2.1 (Aug 5, 2024)
        https://nvmexpress.org/wp-content/uploads/NVM-Express-Base-Specification-Revision-2.1-2024.08.05-Ratified.pdf
    [NVMe-PCIe-1.1] NVMe over PCIe Transport Specification, Revision 1.1 (Aug 5, 2024)
        https://nvmexpress.org/wp-content/uploads/NVM-Express-PCI-Express-Transport-Specification-Revision-1.1-2024.08.05-Ratified.pdf
    [NVM-CommandSet-1.1] NVM Command Set Specification, Revision 1.1 (Aug 5, 2024)
        https://nvmexpress.org/wp-content/uploads/NVM-Express-NVM-Command-Set-Specification-Revision-1.1-2024.08.05-Ratified.pdf
    [PCIe2-0.9] PCI Express(R) 2.0 Base Specification Revision 0.9 (Sep 11, 2006)
        https://community.intel.com/cipcp26785/attachments/cipcp26785/fpga-intellectual-property/8220/1/PCI_Express_Base_Specification_v20.pdf
    [PCI-3.0] PCI Local Bus Specification Revision 3.0 (Feb 3, 2004)
        https://lekensteyn.nl/files/docs/PCI_SPEV_V3_0.pdf
*/

/* ═══════════════════════════════════════════════════════════════════════
 *  Bitfield Helpers
 * ═══════════════════════════════════════════════════════════════════════ */

/* Inclusive bitfield mask helper. */
#define NVME_BITS_MASK(start, end) ((BIT(((end) - (start)) + 1U) - 1U) << (start))

/* ═══════════════════════════════════════════════════════════════════════
 *  Controller Registers
 * ═══════════════════════════════════════════════════════════════════════ */

/* [NVMe-2.1] Section 3.1.4 Controller Properties
    RO = Read Only
    RW = Read Write
    RWC = Read/Write '1' to clear
    RWS = Read/Write '1' to set
*/
typedef struct nvme_controller {
    uint64_t cap;     /* Controller Capabilities (RO) */
    uint32_t vs;      /* Version (RO) */
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

/* Controller Capabilities. [NVMe-2.1 §3.1.4.1, Fig. 36] */
#define NVME_CAP_MQES_MASK      NVME_BITS_MASK(0, 15)   /* Maximum Queue Entries Supported (0-based) */
#define NVME_CAP_NOIOCSS        BIT(37 + 7)             /* No I/O Command Set Support */
#define NVME_CAP_IOCSS          BIT(37 + 6)             /* I/O Command Set Support    */
#define NVME_CAP_NCSS           BIT(37 + 0)             /* NVM Command Set Support    */
#define NVME_CAP_TO_SHIFT       24                      /* Controller Ready Timeout (500 ms units) */
#define NVME_CAP_TO_MASK        NVME_BITS_MASK(24, 31)
#define NVME_CAP_MPSMIN_SHIFT   48                      /* Memory Page Size Minimum   */
#define NVME_CAP_MPSMIN_MASK    NVME_BITS_MASK(48, 51)
#define NVME_CAP_MPSMAX_SHIFT   52                      /* Memory Page Size Maximum   */
#define NVME_CAP_MPSMAX_MASK    NVME_BITS_MASK(52, 55)
#define NVME_CAP_DSTRD_SHIFT    32                      /* Doorbell Stride (2 ^ (2 + DSTRD)) */
#define NVME_CAP_DSTRD_MASK     NVME_BITS_MASK(32, 35)

/* Version. [NVMe-2.1 §3.1.4.2, Fig. 37] */
#define NVME_VS_TER_SHIFT       0
#define NVME_VS_TER             NVME_BITS_MASK(0, 7)    /* Tertiary Version */
#define NVME_VS_MNR_SHIFT       8
#define NVME_VS_MNR             NVME_BITS_MASK(8, 15)   /* Minor Version */
#define NVME_VS_MJR_SHIFT       16
#define NVME_VS_MJR             NVME_BITS_MASK(16, 31)  /* Major Version */

/* Controller Configuration. [NVMe-2.1 §3.1.4.5, Fig. 41] */
#define NVME_CC_IOCQES_SHIFT    20                      /* I/O CQ Entry Size (2^IOCQES bytes) */
#define NVME_CC_IOCQES_MASK     NVME_BITS_MASK(20, 23)
#define NVME_CC_IOSQES_SHIFT    16                      /* I/O SQ Entry Size (2^IOSQES bytes) */
#define NVME_CC_IOSQES_MASK     NVME_BITS_MASK(16, 19)
#define NVME_CC_MPS_SHIFT       7                       /* Host Memory Page Size (2^(12+MPS) bytes) */
#define NVME_CC_MPS_MASK        NVME_BITS_MASK(7, 10)
#define NVME_CC_CSS_SHIFT       4                       /* I/O Command Set Selected */
#define NVME_CC_CSS_MASK        NVME_BITS_MASK(4, 6)
#define NVME_CC_CSS_NVM         0x0U                    /* NVM Command Set */
#define NVME_CC_EN              BIT(0)                  /* Controller Enable */

/* Controller Status. [NVMe-2.1 §3.1.4.6, Fig. 42] */
#define NVME_CSTS_RDY           BIT(0)                  /* Controller Ready */

/* NVM Subsystem Reset. [NVMe-2.1 §3.1.4.7, Fig. 43] */
#define NVME_NSSRC_VALUE        (0x4E564D65)            /* NVM Subsystem Reset Control - Reset value */

/* Admin Queue Attributes. [NVMe-2.1 §3.1.4.8, Fig. 44] */
#define NVME_AQA_ACQS_SHIFT     16                      /* Admin Completion Queue Size (#entries) */
#define NVME_AQA_ACQS_MASK      NVME_BITS_MASK(16, 27)
#define NVME_AQA_ASQS_SHIFT     0                       /* Admin Submission Queue Size (#entries) */
#define NVME_AQA_ASQS_MASK      NVME_BITS_MASK(0, 11)

/* Doorbell stride in bytes = 2^(2 + DSTRD). [NVMe-2.1 §3.1.4.1, Fig. 36] */
#define NVME_DOORBELL_STRIDE_BYTES(DSTRD) (4U << (DSTRD))

/*
 * Doorbell offsets. [NVMe-PCIe-1.1 §3.1.2, Fig. 4-6]
 * - SQyTDBL offset = 1000h + ((2y)   * stride)
 * - CQyHDBL offset = 1000h + ((2y+1) * stride)
 */
#define NVME_PCIE_SQTDBL_OFFSET(queue_id, DSTRD) \
    (0x1000U + ((2U * (uint32_t)(queue_id)) * NVME_DOORBELL_STRIDE_BYTES(DSTRD)))
#define NVME_PCIE_CQHDBL_OFFSET(queue_id, DSTRD) \
    (0x1000U + (((2U * (uint32_t)(queue_id)) + 1U) * NVME_DOORBELL_STRIDE_BYTES(DSTRD)))

/* ═══════════════════════════════════════════════════════════════════════
 *  Commands / SQE / CQE
 * ═══════════════════════════════════════════════════════════════════════ */

/* [NVMe-2.1] 4.1 Submission Queue Entry */
typedef struct nvme_submission_queue_entry {
    uint32_t cdw0;  /* Command Dword 0 (common) */
    uint32_t nsid;  /* Namespace Identifier */
    uint32_t cdw2;  /* Command Dword 2 (command-specific) */
    uint32_t cdw3;  /* Command Dword 3 (command-specific) */
    uint64_t mptr;  /* Metadata Pointer */
    uint64_t prp1;  /* Data Pointer - PRP Entry 1 */
    uint64_t prp2;  /* Data Pointer - PRP Entry 2 */
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

/* ═══════════════════════════════════════════════════════════════════════
 *  PCIe Transport
 * ═══════════════════════════════════════════════════════════════════════ */

/* I/O Port Configuration */
#define PCI_CONFIG_ADDR_IOPORT_ID 1
#define PCI_CONFIG_DATA_IOPORT_ID 2
#define PCI_CONFIG_ADDR_PORT 0xCF8
#define PCI_CONFIG_DATA_PORT 0xCFC

static inline uint32_t pci_config_read_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset)
{
    uint32_t address = (uint32_t)((uint32_t)bus << 16) | ((uint32_t)dev << 11) | ((uint32_t)func << 8) | (offset & 0xfc)
                     | ((uint32_t)0x80000000);
    microkit_x86_ioport_write_32(PCI_CONFIG_ADDR_IOPORT_ID, PCI_CONFIG_ADDR_PORT, address);
    return microkit_x86_ioport_read_32(PCI_CONFIG_DATA_IOPORT_ID, PCI_CONFIG_DATA_PORT);
}

static inline void pci_config_write_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset, uint32_t value)
{
    uint32_t address = (uint32_t)((uint32_t)bus << 16) | ((uint32_t)dev << 11) | ((uint32_t)func << 8) | (offset & 0xfc)
                     | ((uint32_t)0x80000000);
    microkit_x86_ioport_write_32(PCI_CONFIG_ADDR_IOPORT_ID, PCI_CONFIG_ADDR_PORT, address);
    microkit_x86_ioport_write_32(PCI_CONFIG_DATA_IOPORT_ID, PCI_CONFIG_DATA_PORT, value);
}

/* ═══════════════════════════════════════════════════════════════════════
 *  Platform Constants
 * ═══════════════════════════════════════════════════════════════════════ */

#define NVME_ADMIN_QUEUE_SIZE 0x1000
#define NVME_IO_QUEUE_SIZE    0x1000

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
