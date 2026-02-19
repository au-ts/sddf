/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/*
 * NVMe command opcodes, submission and completion queue entry structures,
 * CDW field encodings, and SGL descriptor definitions.
 */

#include <stdbool.h>
#include <stdint.h>
#include "nvme_bits.h"

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
#define NVME_CREATE_IO_Q_CDW10_QID_MASK    NVME_BITS_MASK(0, 15)
#define NVME_CREATE_IO_Q_CDW10_QSIZE_SHIFT 16
#define NVME_CREATE_IO_Q_CDW10_QSIZE_MASK  NVME_BITS_MASK(16, 31)

static inline uint32_t nvme_build_create_io_q_cdw10(uint16_t qid, uint16_t qsize)
{
    return (((uint32_t)qsize << NVME_CREATE_IO_Q_CDW10_QSIZE_SHIFT) & NVME_CREATE_IO_Q_CDW10_QSIZE_MASK)
         | (((uint32_t)qid << NVME_CREATE_IO_Q_CDW10_QID_SHIFT) & NVME_CREATE_IO_Q_CDW10_QID_MASK);
}

/* Create I/O CQ CDW11 fields. [NVMe-2.1 §5.2.1, Fig. 475] */
#define NVME_CREATE_IO_CQ_CDW11_PC       BIT(0)
#define NVME_CREATE_IO_CQ_CDW11_IEN      BIT(1)
#define NVME_CREATE_IO_CQ_CDW11_IV_SHIFT 16
#define NVME_CREATE_IO_CQ_CDW11_IV_MASK  NVME_BITS_MASK(16, 31)

static inline uint32_t nvme_build_create_io_cq_cdw11(uint16_t iv, bool ien, bool pc)
{
    return (((uint32_t)iv << NVME_CREATE_IO_CQ_CDW11_IV_SHIFT) & NVME_CREATE_IO_CQ_CDW11_IV_MASK)
         | (ien ? NVME_CREATE_IO_CQ_CDW11_IEN : 0U) | (pc ? NVME_CREATE_IO_CQ_CDW11_PC : 0U);
}

/* Create I/O SQ CDW11 fields. [NVMe-2.1 §5.2.2, Fig. 479] */
#define NVME_CREATE_IO_SQ_CDW11_PC          BIT(0)
#define NVME_CREATE_IO_SQ_CDW11_QPRIO_SHIFT 1
#define NVME_CREATE_IO_SQ_CDW11_QPRIO_MASK  NVME_BITS_MASK(1, 2)
#define NVME_CREATE_IO_SQ_CDW11_CQID_SHIFT  16
#define NVME_CREATE_IO_SQ_CDW11_CQID_MASK   NVME_BITS_MASK(16, 31)

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
#define NVME_RW_CDW12_NLB_MASK NVME_BITS_MASK(0, 15)
#define NVME_RW_CDW12_LR       BIT(31)

static inline uint32_t nvme_build_rw_cdw12(uint16_t nlb, bool lr)
{
    return ((uint32_t)nlb & NVME_RW_CDW12_NLB_MASK) | (lr ? NVME_RW_CDW12_LR : 0U);
}

/* Admin and I/O commands use the common 64-byte SQE layout. [NVMe-2.1 §4.1.1, Fig. 92] */
typedef struct nvme_submission_queue_entry {
    uint32_t cdw0;  /* Command Dword 0 (field layout in [NVMe-2.1 Fig. 91]) */
    uint32_t nsid;  /* Namespace Identifier */
    uint32_t cdw2;  /* Command Dword 2 (command-specific) */
    uint32_t cdw3;  /* Command Dword 3 (command-specific) */
    uint64_t mptr;  /* Metadata Pointer */
    uint64_t dptr1; /* Data Pointer (PRP1 or SGL1 bytes 0..7) */
    uint64_t dptr2; /* Data Pointer (PRP2 or SGL1 bytes 8..15) */
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
#define NVME_CDW0_OPCODE_MASK NVME_BITS_MASK(0, 7)

/*
 * CID occupies bits 31:16 and must be unique among outstanding queue commands.
 * CID 0xFFFF is reserved for non-command-specific Error Information entries. [NVMe-2.1 Fig. 91]
 */
#define NVME_CDW0_CID_SHIFT 16
#define NVME_CDW0_CID_MASK  NVME_BITS_MASK(16, 31)

/* PSDT (bits 15:14) selects PRP vs SGL data pointers. [NVMe-2.1 Fig. 91] */
#define NVME_CDW0_PSDT_SHIFT 14
#define NVME_CDW0_PSDT_MASK  NVME_BITS_MASK(14, 15)
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
    uint32_t cdw0;                 /* DW0 command-specific result */
    uint32_t cdw1;                 /* DW1 command-specific result */
    uint16_t sqhd;                 /* DW2 bits 15:00 SQ Head Pointer */
    uint16_t sqid;                 /* DW2 bits 31:16 SQ Identifier */
    uint16_t cid;                  /* DW3 bits 15:00 Command Identifier */
    uint16_t phase_tag_and_status; /* DW3 bits 31:16: P at bit 16 and STATUS at bits 31:17 */
} nvme_completion_queue_entry_t;
_Static_assert(sizeof(nvme_completion_queue_entry_t) == 16,
               "The Common Completion Queue Entry Layout is 16 bytes in size");

/*
 * DW3 layout is STATUS[31:17], P[16], CID[15:0]; this header stores DW3[31:16] in
 * phase_tag_and_status, so P maps to bit 0 and STATUS maps to bits 15:01.
 * [NVMe-2.1 §4.2.1, Fig. 98; §4.2.3, Fig. 100]
 */
#define NVME_CQE_PHASE_MASK BIT(0)
#define NVME_CQE_STATUS_SHIFT 1
#define NVME_CQE_STATUS_MASK  NVME_BITS_MASK(1, 15)

/* Generic SGL descriptor format. [NVMe-2.1 §4.3.2, Fig. 114] */
#define NVME_SGL_ID_TYPE_SHIFT     4
#define NVME_SGL_ID_SUBTYPE_SHIFT  0
#define NVME_SGL_ID_TYPE_MASK      NVME_BITS_MASK(4, 7)
#define NVME_SGL_ID_SUBTYPE_MASK   NVME_BITS_MASK(0, 3)
#define NVME_SGL_ID(type, subtype) ((((type) & 0xFU) << NVME_SGL_ID_TYPE_SHIFT) | (((subtype) & 0xFU) << NVME_SGL_ID_SUBTYPE_SHIFT))
#define NVME_SGL_DPTR2_ID_SHIFT    56 /* ID occupies dptr2[63:56] */

/* SGL Descriptor Type - currently only Data Block is supported. [NVMe-2.1 Fig. 115] */
#define NVME_SGL_TYPE_DATA_BLOCK 0x0

/* SGL Descriptor Sub Type - currently only Address is supported. [NVMe-2.1 Fig. 116] */
#define NVME_SGL_SUBTYPE_ADDRESS 0x0

/* Dword alignment mask: (x & mask) != 0 indicates misalignment. [NVMe-2.1 §4.3.2] */
#define NVME_SGL_DWORD_ALIGN_MASK 0x3U
