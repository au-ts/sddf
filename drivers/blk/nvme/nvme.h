/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
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

// clang-format off
#define LOG_NVME_ERR(...) do{ sddf_dprintf("NVME|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)
// clang-format on

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
#define NVME_CAP_MQES_MASK      BIT_MASK(0, 15) /* Maximum Queue Entries Supported (0-based) */
#define NVME_CAP_NOIOCSS        BIT(37 + 7) /* No I/O Command Set Support */
#define NVME_CAP_IOCSS          BIT(37 + 6) /* I/O Command Set Support    */
#define NVME_CAP_NCSS           BIT(37 + 0) /* NVM Command Set Support    */
#define NVME_CAP_TO_SHIFT       24 /* Controller Ready Timeout (500 ms units) */
#define NVME_CAP_TO_MASK        BIT_MASK(24, 31)
#define NVME_CAP_MPSMIN_SHIFT   48 /* Memory Page Size Minimum   */
#define NVME_CAP_MPSMIN_MASK    BIT_MASK(48, 51)
#define NVME_CAP_MPSMAX_SHIFT   52 /* Memory Page Size Maximum   */
#define NVME_CAP_MPSMAX_MASK    BIT_MASK(52, 55)
#define NVME_CAP_DSTRD_SHIFT    32 /* Doorbell Stride (2 ^ (2 + DSTRD)) */
#define NVME_CAP_DSTRD_MASK     BIT_MASK(32, 35)

/* Version. [NVMe-2.1 §3.1.4.2, Fig. 37] */
#define NVME_VS_TER_SHIFT       0
#define NVME_VS_TER             BIT_MASK(0, 7) /* Tertiary Version */
#define NVME_VS_MNR_SHIFT       8
#define NVME_VS_MNR             BIT_MASK(8, 15) /* Minor Version */
#define NVME_VS_MJR_SHIFT       16
#define NVME_VS_MJR             BIT_MASK(16, 31) /* Major Version */

/* Controller Configuration. [NVMe-2.1 §3.1.4.5, Fig. 41] */
#define NVME_CC_IOCQES_SHIFT    20 /* I/O CQ Entry Size (2^IOCQES bytes) */
#define NVME_CC_IOCQES_MASK     BIT_MASK(20, 23)
#define NVME_CC_IOSQES_SHIFT    16 /* I/O SQ Entry Size (2^IOSQES bytes) */
#define NVME_CC_IOSQES_MASK     BIT_MASK(16, 19)
#define NVME_CC_MPS_SHIFT       7 /* Host Memory Page Size (2^(12+MPS) bytes) */
#define NVME_CC_MPS_MASK        BIT_MASK(7, 10)
#define NVME_CC_CSS_SHIFT       4 /* I/O Command Set Selected */
#define NVME_CC_CSS_MASK        BIT_MASK(4, 6)
#define NVME_CC_CSS_NVM         0x0U /* NVM Command Set */
#define NVME_CC_EN              BIT(0) /* Controller Enable */

/* Controller Status. [NVMe-2.1 §3.1.4.6, Fig. 42] */
#define NVME_CSTS_RDY           BIT(0) /* Controller Ready */

/* NVM Subsystem Reset. [NVMe-2.1 §3.1.4.7, Fig. 43] */
#define NVME_NSSRC_VALUE        (0x4E564D65) /* NVM Subsystem Reset Control - Reset value */

/* Admin Queue Attributes. [NVMe-2.1 §3.1.4.8, Fig. 44] */
#define NVME_AQA_ACQS_SHIFT     16 /* Admin Completion Queue Size (#entries) */
#define NVME_AQA_ACQS_MASK      BIT_MASK(16, 27)
#define NVME_AQA_ASQS_SHIFT     0 /* Admin Submission Queue Size (#entries) */
#define NVME_AQA_ASQS_MASK      BIT_MASK(0, 11)

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

/*
 * Opcodes used by this driver.
 * [NVMe-2.1 §7.2, §5.1.12, §5.1.13, §5.2.1, §5.2.2]
 * [NVM-CommandSet-1.1 §3.3.4, §3.3.6]
 */
#define NVME_OP_FLUSH 0x00
#define NVME_OP_WRITE 0x01
#define NVME_OP_READ  0x02

#define NVME_ADMIN_OP_CREATE_IO_SQ 0x01
#define NVME_ADMIN_OP_GET_LOG_PAGE 0x02
#define NVME_ADMIN_OP_CREATE_IO_CQ 0x05
#define NVME_ADMIN_OP_IDENTIFY     0x06

/*
 * Create I/O CQ and SQ CDW10 fields (identical layout). [NVMe-2.1 §5.2.1, Fig. 474; §5.2.2, Fig. 478]
 * QSIZE is 0-based (actual depth = QSIZE + 1).
 */
#define NVME_CREATE_IO_Q_CDW10_QID_SHIFT   0
#define NVME_CREATE_IO_Q_CDW10_QID_MASK    BIT_MASK(0, 15)
#define NVME_CREATE_IO_Q_CDW10_QSIZE_SHIFT 16
#define NVME_CREATE_IO_Q_CDW10_QSIZE_MASK  BIT_MASK(16, 31)

static inline uint32_t nvme_build_create_io_q_cdw10(uint16_t qid, uint16_t qsize)
{
    return (((uint32_t)qsize << NVME_CREATE_IO_Q_CDW10_QSIZE_SHIFT) & NVME_CREATE_IO_Q_CDW10_QSIZE_MASK)
         | (((uint32_t)qid << NVME_CREATE_IO_Q_CDW10_QID_SHIFT) & NVME_CREATE_IO_Q_CDW10_QID_MASK);
}

/* Create I/O CQ CDW11 fields. [NVMe-2.1 §5.2.1, Fig. 475] */
#define NVME_CREATE_IO_CQ_CDW11_PC       BIT(0)
#define NVME_CREATE_IO_CQ_CDW11_IEN      BIT(1)
#define NVME_CREATE_IO_CQ_CDW11_IV_SHIFT 16
#define NVME_CREATE_IO_CQ_CDW11_IV_MASK  BIT_MASK(16, 31)

static inline uint32_t nvme_build_create_io_cq_cdw11(uint16_t iv, bool ien, bool pc)
{
    return (((uint32_t)iv << NVME_CREATE_IO_CQ_CDW11_IV_SHIFT) & NVME_CREATE_IO_CQ_CDW11_IV_MASK)
         | (ien ? NVME_CREATE_IO_CQ_CDW11_IEN : 0U) | (pc ? NVME_CREATE_IO_CQ_CDW11_PC : 0U);
}

/* Create I/O SQ CDW11 fields. [NVMe-2.1 §5.2.2, Fig. 479] */
#define NVME_CREATE_IO_SQ_CDW11_PC          BIT(0)
#define NVME_CREATE_IO_SQ_CDW11_QPRIO_SHIFT 1
#define NVME_CREATE_IO_SQ_CDW11_QPRIO_MASK  BIT_MASK(1, 2)
#define NVME_CREATE_IO_SQ_CDW11_CQID_SHIFT  16
#define NVME_CREATE_IO_SQ_CDW11_CQID_MASK   BIT_MASK(16, 31)

/* Create I/O SQ QPRIO values. [NVMe-2.1 §5.2.2, Fig. 479] */
#define NVME_CREATE_IO_SQ_QPRIO_URGENT    0x0
#define NVME_CREATE_IO_SQ_QPRIO_HIGH      0x1
#define NVME_CREATE_IO_SQ_QPRIO_MEDIUM    0x2
#define NVME_CREATE_IO_SQ_QPRIO_LOW       0x3

static inline uint32_t nvme_build_create_io_sq_cdw11(uint16_t cqid, uint8_t qprio, bool pc)
{
    return (((uint32_t)cqid << NVME_CREATE_IO_SQ_CDW11_CQID_SHIFT) & NVME_CREATE_IO_SQ_CDW11_CQID_MASK)
         | (((uint32_t)qprio << NVME_CREATE_IO_SQ_CDW11_QPRIO_SHIFT) & NVME_CREATE_IO_SQ_CDW11_QPRIO_MASK)
         | (pc ? NVME_CREATE_IO_SQ_CDW11_PC : 0U);
}

/* NVM Read/Write CDW12 fields. [NVM-CommandSet-1.1 §3.3.4, Fig. 53; §3.3.6, Fig. 70] */
#define NVME_RW_CDW12_NLB_MASK BIT_MASK(0, 15)
#define NVME_RW_CDW12_LR       BIT(31)

static inline uint32_t nvme_build_rw_cdw12(uint16_t nlb, bool lr)
{
    return ((uint32_t)nlb & NVME_RW_CDW12_NLB_MASK) | (lr ? NVME_RW_CDW12_LR : 0U);
}

/* Admin and I/O commands use the common 64-byte SQE layout. [NVMe-2.1 §4.1.1, Fig. 92] */
typedef struct nvme_submission_queue_entry {
    uint32_t cdw0;  /* Command Dword 0 (common) */
    uint32_t nsid;  /* Namespace Identifier */
    uint32_t cdw2;  /* Command Dword 2 (command-specific) */
    uint32_t cdw3;  /* Command Dword 3 (command-specific) */
    uint64_t mptr;  /* Metadata Pointer */
    uint64_t dptr1; /* Data Pointer - PRP Entry 1 */
    uint64_t dptr2; /* Data Pointer - PRP Entry 2 */
    uint32_t cdw10; /* Command Dword 10 (command-specific) */
    uint32_t cdw11; /* Command Dword 11 (command-specific) */
    uint32_t cdw12; /* Command Dword 12 (command-specific) */
    uint32_t cdw13; /* Command Dword 13 (command-specific) */
    uint32_t cdw14; /* Command Dword 14 (command-specific) */
    uint32_t cdw15; /* Command Dword 15 (command-specific) */
} nvme_submission_queue_entry_t;
_Static_assert(sizeof(nvme_submission_queue_entry_t) == 64, "Each Common Command Format command is 64 bytes in size.");

/*
 * CDW0 fields used by this driver: Opcode, PSDT, and CID.
 * FUSE (bits 9:8) is currently not used. [NVMe-2.1 §4.1.1, Fig. 91]
 */
#define NVME_CDW0_OPCODE_MASK BIT_MASK(0, 7)

/*
 * CID occupies bits 31:16 and must be unique among outstanding queue commands.
 * CID 0xFFFF is reserved for non-command-specific Error Information entries. [NVMe-2.1 Fig. 91]
 */
#define NVME_CDW0_CID_SHIFT 16
#define NVME_CDW0_CID_MASK  BIT_MASK(16, 31)

/* PSDT (bits 15:14) selects PRP vs SGL data pointers. [NVMe-2.1 Fig. 91] */
#define NVME_CDW0_PSDT_SHIFT 14
#define NVME_CDW0_PSDT_MASK  BIT_MASK(14, 15)
/* 00b: use PRPs. */
#define NVME_CDW0_PSDT_PRP             0x0U
/* 01b: use SGLs, MPTR points to one contiguous physical metadata buffer. */
#define NVME_CDW0_PSDT_SGL_MPTR_CONTIG 0x1U
/* 10b: use SGLs, MPTR points to an SGL segment containing one SGL descriptor. */
#define NVME_CDW0_PSDT_SGL_MPTR_SGL    0x2U
/* 11b: reserved by spec. */

static inline uint32_t nvme_build_cdw0(uint16_t cid, uint8_t opcode, uint32_t psdt)
{
    return (((uint32_t)cid << NVME_CDW0_CID_SHIFT) & NVME_CDW0_CID_MASK) | ((uint32_t)opcode & NVME_CDW0_OPCODE_MASK)
         | ((psdt << NVME_CDW0_PSDT_SHIFT) & NVME_CDW0_PSDT_MASK);
}

/*
 * Admin and I/O completions use the common 16-byte CQE layout.
 * [NVMe-2.1 §4.2.1, Fig. 96, Fig. 97, Fig. 98]
 */
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

/* Generic SGL descriptor format. [NVMe-2.1 §4.3.2, Fig. 114] */
#define NVME_SGL_ID_TYPE_SHIFT     4
#define NVME_SGL_ID_SUBTYPE_SHIFT  0
#define NVME_SGL_ID_TYPE_MASK      BIT_MASK(4, 7)
#define NVME_SGL_ID_SUBTYPE_MASK   BIT_MASK(0, 3)
#define NVME_SGL_ID(type, subtype) ((((type) & 0xFU) << NVME_SGL_ID_TYPE_SHIFT) | (((subtype) & 0xFU) << NVME_SGL_ID_SUBTYPE_SHIFT))
#define NVME_SGL_DPTR2_ID_SHIFT    56 /* ID occupies dptr2[63:56] */

/* SGL Descriptor Type - currently only Data Block is supported. [NVMe-2.1 Fig. 115] */
#define NVME_SGL_TYPE_DATA_BLOCK 0x0

/* SGL Descriptor Sub Type - currently only Address is supported. [NVMe-2.1 Fig. 116] */
#define NVME_SGL_SUBTYPE_ADDRESS 0x0

/* Dword alignment mask: (x & mask) != 0 indicates misalignment. [NVMe-2.1 §4.3.2] */
#define NVME_SGL_DWORD_ALIGN_MASK 0x3U

/* ═══════════════════════════════════════════════════════════════════════
 *  Identify Structures
 * ═══════════════════════════════════════════════════════════════════════ */

/* Identify CNS values used by this driver. [NVMe-2.1 §5.1.13, Fig. 310] */
#define NVME_IDENTIFY_CNS_NAMESPACE  0x00U
#define NVME_IDENTIFY_CNS_CONTROLLER 0x01U

/*
 * Identify Controller (I/O Command Set Independent) response for CNS=01h.
 * Currently unused fields are modeled as reserved spans while preserving spec-defined offsets.
 * [NVMe-2.1 §5.1.13.2.1, Fig. 312]
 */
typedef struct nvme_identify_ctrl {
    uint16_t vid; /* PCI Vendor ID */
    uint16_t ssvid; /* PCI Subsystem Vendor ID */
    char sn[20]; /* Serial Number (ASCII, space-padded) */
    char mn[40]; /* Model Number (ASCII, space-padded) */
    char fr[8]; /* Firmware Revision (ASCII) */
    uint8_t _reserved0[77 - 72];
    uint8_t mdts; /* Max transfer size exponent (0h means no limit; units based on CAP.MPSMIN) */
    uint8_t _reserved1[96 - 78];
    uint32_t ctratt; /* Controller Attributes (MEM bit 16 affects MDTS metadata accounting) */
    uint8_t _reserved2[512 - 100];
    uint8_t sqes; /* MINSQES[3:0], MAXSQES[7:4] (required value is 6 => 64-byte SQE) */
    uint8_t cqes; /* MINCQES[3:0], MAXCQES[7:4] (required value is 4 => 16-byte CQE) */
    uint8_t _reserved3[536 - 514];
    uint32_t sgls; /* SGL Support */
    uint8_t _reserved4[4096 - 540];
} nvme_identify_ctrl_t;
_Static_assert(sizeof(nvme_identify_ctrl_t) == 4096, "Identify Controller data structure must be 4096 bytes");
_Static_assert(offsetof(nvme_identify_ctrl_t, vid) == 0, "VID must be at byte offset 0");
_Static_assert(offsetof(nvme_identify_ctrl_t, ssvid) == 2, "SSVID must be at byte offset 2");
_Static_assert(offsetof(nvme_identify_ctrl_t, sn) == 4, "SN must be at byte offset 4");
_Static_assert(offsetof(nvme_identify_ctrl_t, mn) == 24, "MN must be at byte offset 24");
_Static_assert(offsetof(nvme_identify_ctrl_t, fr) == 64, "FR must be at byte offset 64");
_Static_assert(offsetof(nvme_identify_ctrl_t, mdts) == 77, "MDTS must be at byte offset 77");
_Static_assert(offsetof(nvme_identify_ctrl_t, ctratt) == 96, "CTRATT must be at byte offset 96");
_Static_assert(offsetof(nvme_identify_ctrl_t, sqes) == 512, "SQES must be at byte offset 512");
_Static_assert(offsetof(nvme_identify_ctrl_t, cqes) == 513, "CQES must be at byte offset 513");
_Static_assert(offsetof(nvme_identify_ctrl_t, sgls) == 536, "SGLS must be at byte offset 536");

/* Min/max SQES/CQES (min in bits 3:0, max in bits 7:4). [NVMe-2.1 Fig. 312] */
#define NVME_IDENTIFY_ENTRY_SIZE_MIN_SHIFT 0
#define NVME_IDENTIFY_ENTRY_SIZE_MIN_MASK  BIT_MASK(0, 3)
#define NVME_IDENTIFY_ENTRY_SIZE_MAX_SHIFT 4
#define NVME_IDENTIFY_ENTRY_SIZE_MAX_MASK  BIT_MASK(4, 7)

/* LBA Format entry layout. [NVM-CommandSet-1.1 Fig. 116] */
typedef struct nvme_lba_format {
    uint16_t ms;
    uint8_t lbads; /* 2^LBADS bytes; values < 9 are invalid. */
    uint8_t rp; /* Bits 1:0 are RP; upper bits are reserved. */
} nvme_lba_format_t;
_Static_assert(sizeof(nvme_lba_format_t) == 4, "Each LBAF entry is 4 bytes");

/*
 * Identify Namespace response for NVM Command Set (CNS=00h).
 * Currently unused fields are modeled as reserved spans while preserving spec-defined offsets.
 * [NVM-CommandSet-1.1 §4.1.5.1, Fig. 114]
 */
typedef struct nvme_identify_ns {
    uint64_t nsze;
    uint8_t _reserved0[26 - 8];
    uint8_t flbas;
    uint8_t _reserved1[128 - 27];
    nvme_lba_format_t lbaf[64]; /* 64 LBA format descriptors */
    uint8_t _reserved2[4096 - 384];
} nvme_identify_ns_t;
_Static_assert(sizeof(nvme_identify_ns_t) == 4096, "Identify Namespace (CNS=00h) data structure must be 4096 bytes");
_Static_assert(offsetof(nvme_identify_ns_t, nsze) == 0, "NSZE must be at byte offset 0");
_Static_assert(offsetof(nvme_identify_ns_t, flbas) == 26, "FLBAS must be at byte offset 26");
_Static_assert(offsetof(nvme_identify_ns_t, lbaf) == 128, "LBAF array must start at byte offset 128");

/* FLBAS field layout. [NVM-CommandSet-1.1 §4.1.5.1, Fig. 114] */
#define NVME_IDENTIFY_FLBAS_FIDXL_MASK  BIT_MASK(0, 3)
#define NVME_IDENTIFY_FLBAS_FIDXU_SHIFT 5
#define NVME_IDENTIFY_FLBAS_FIDXU_MASK  BIT_MASK(5, 6)

static inline uint8_t nvme_identify_flbas_format_index(uint8_t flbas)
{
    uint8_t idx_low = (uint8_t)(flbas & NVME_IDENTIFY_FLBAS_FIDXL_MASK);
    uint8_t idx_high = (uint8_t)(((flbas & NVME_IDENTIFY_FLBAS_FIDXU_MASK) >> NVME_IDENTIFY_FLBAS_FIDXU_SHIFT) << 4);
    return (uint8_t)(idx_low | idx_high);
}

/* SGLS bits 1:0 transport encoding. [NVMe-2.1 Fig. 312] */
#define NVME_IDENTIFY_SGLS_TRANSPORT_MASK          BIT_MASK(0, 1)
#define NVME_IDENTIFY_SGLS_TRANSPORT_BYTE_ALIGNED  BIT(0)
#define NVME_IDENTIFY_SGLS_TRANSPORT_DWORD_ALIGNED BIT(1)

/* ═══════════════════════════════════════════════════════════════════════
 *  PCIe Transport
 * ═══════════════════════════════════════════════════════════════════════ */

/* PCI Configuration Mechanism #1 I/O ports. [PCI-3.0 §3.2.2.3.2] */
/* I/O Port Configuration */
#define NVME_PCI_CONFIG_ADDR_IOPORT_ID 1
#define NVME_PCI_CONFIG_DATA_IOPORT_ID 2
#define NVME_PCI_CFG_ADDR_PORT         0xCF8
#define NVME_PCI_CFG_DATA_PORT         0xCFC

/* PCI config address encoding. [PCI-3.0 §3.2.2.3.2] */
#define NVME_PCIE_CFG_ADDR_ENABLE      BIT(31)
#define NVME_PCIE_CFG_ADDR_BUS_SHIFT   16
#define NVME_PCIE_CFG_ADDR_DEV_SHIFT   11
#define NVME_PCIE_CFG_ADDR_FUNC_SHIFT  8
#define NVME_PCIE_CFG_ADDR_OFFSET_MASK 0xFC

/* Type 0/1 configuration space register offsets. [NVMe-PCIe-1.1 §3.8.1, Fig. 10] */
#define NVME_PCIE_CFG_OFFSET_ID          0x00
#define NVME_PCIE_CFG_OFFSET_COMMAND     0x04
#define NVME_PCIE_CFG_OFFSET_BAR0        0x10
#define NVME_PCIE_CFG_OFFSET_INTR_INFO   0x3C

/* Interrupt information field layout. [PCIe2-0.9 §7.5.1.20] */
#define NVME_PCIE_INTR_LINE_MASK  BIT_MASK(0, 7)
#define NVME_PCIE_INTR_PIN_SHIFT  8U
#define NVME_PCIE_INTR_PIN_MASK   BIT_MASK(8, 15)

static inline uint32_t nvme_pcie_cfg_address(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset)
{
    return NVME_PCIE_CFG_ADDR_ENABLE | ((uint32_t)bus << NVME_PCIE_CFG_ADDR_BUS_SHIFT)
         | ((uint32_t)dev << NVME_PCIE_CFG_ADDR_DEV_SHIFT) | ((uint32_t)func << NVME_PCIE_CFG_ADDR_FUNC_SHIFT)
         | ((uint32_t)offset & NVME_PCIE_CFG_ADDR_OFFSET_MASK);
}

static inline uint32_t pci_config_read_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset)
{
    uint32_t address = nvme_pcie_cfg_address(bus, dev, func, offset);
    microkit_x86_ioport_write_32(NVME_PCI_CONFIG_ADDR_IOPORT_ID, NVME_PCI_CFG_ADDR_PORT, address);
    return microkit_x86_ioport_read_32(NVME_PCI_CONFIG_DATA_IOPORT_ID, NVME_PCI_CFG_DATA_PORT);
}

static inline void pci_config_write_32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset, uint32_t value)
{
    uint32_t address = nvme_pcie_cfg_address(bus, dev, func, offset);
    microkit_x86_ioport_write_32(NVME_PCI_CONFIG_ADDR_IOPORT_ID, NVME_PCI_CFG_ADDR_PORT, address);
    microkit_x86_ioport_write_32(NVME_PCI_CONFIG_DATA_IOPORT_ID, NVME_PCI_CFG_DATA_PORT, value);
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
#define NVME_CONTROLLER_VADDR 0x20000000
#define NVME_ASQ_VADDR        0x20100000
#define NVME_ACQ_VADDR        0x20101000
#define NVME_IO_SQ_VADDR      0x20102000
#define NVME_IO_CQ_VADDR      0x20103000
#define NVME_IDENTIFY_VADDR   0x20104000
#define NVME_PRP_LIST_VADDR   0x20200000

/* Memory Region Physical Addresses */
#define NVME_ASQ_PADDR        0x5FDF0000
#define NVME_ACQ_PADDR        0x5FDF1000
#define NVME_IO_SQ_PADDR      0x5FDF2000
#define NVME_IO_CQ_PADDR      0x5FDF3000
#define NVME_IDENTIFY_PADDR   0x5FDF4000
#define NVME_PRP_LIST_PADDR   0x5FE00000

/* Memory Region Sizes. */
#define NVME_ASQ_REGION_SIZE        0x1000
#define NVME_ACQ_REGION_SIZE        0x1000
#define NVME_IO_SQ_REGION_SIZE      0x1000
#define NVME_IO_CQ_REGION_SIZE      0x1000
#define NVME_IDENTIFY_REGION_SIZE   0x2000
#define NVME_PRP_LIST_REGION_SIZE   0x80000

/* Identify response buffers (one page each). */
#define NVME_IDENTIFY_BUFFER_BYTES 0x1000
#define NVME_IDENTIFY_CTRL_VADDR   (NVME_IDENTIFY_VADDR)
#define NVME_IDENTIFY_CTRL_PADDR   (NVME_IDENTIFY_PADDR)
#define NVME_IDENTIFY_NS_VADDR     (NVME_IDENTIFY_VADDR + NVME_IDENTIFY_BUFFER_BYTES)
#define NVME_IDENTIFY_NS_PADDR     (NVME_IDENTIFY_PADDR + NVME_IDENTIFY_BUFFER_BYTES)

#define NVME_IRQ 17

/* Host page size exponent; CC.MPS encodes page size as 2^(12 + MPS). [NVMe-2.1 §3.1.4.5, Fig. 41] */
#define NVME_PAGE_SIZE_LOG2 12

/* Queue structures must fit their dedicated queue regions. */
_Static_assert(NVME_ADMIN_QUEUE_SIZE <= NVME_ASQ_REGION_SIZE, "ASQ allocation exceeds nvme_admin_sq region size");
_Static_assert(NVME_ADMIN_QUEUE_SIZE <= NVME_ACQ_REGION_SIZE, "ACQ allocation exceeds nvme_admin_cq region size");
_Static_assert(NVME_IO_QUEUE_SIZE <= NVME_IO_SQ_REGION_SIZE, "IO SQ allocation exceeds nvme_io_sq region size");
_Static_assert(NVME_IO_QUEUE_SIZE <= NVME_IO_CQ_REGION_SIZE, "IO CQ allocation exceeds nvme_io_cq region size");

/* Identify buffers must fit in their shared region and not overlap. */
_Static_assert(sizeof(nvme_identify_ctrl_t) <= NVME_IDENTIFY_BUFFER_BYTES,
               "Identify Controller structure must fit within one Identify buffer");
_Static_assert(NVME_IDENTIFY_CTRL_VADDR + NVME_IDENTIFY_BUFFER_BYTES <= NVME_IDENTIFY_NS_VADDR,
               "Identify Controller buffer must not overlap Identify Namespace buffer");
_Static_assert((2 * NVME_IDENTIFY_BUFFER_BYTES) <= NVME_IDENTIFY_REGION_SIZE,
               "NVMe identify region must fit both Identify buffers");
