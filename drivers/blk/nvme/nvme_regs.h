/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/*
 * NVMe controller register layout and bitfield definitions.
 * Covers CAP, CC, CSTS, AQA, and doorbell offset calculations.
 */

#include <stdint.h>
#include <stddef.h>
#include "nvme_bits.h"

/* Controller Properties. [NVMe-2.1 §3.1.4] */
typedef struct nvme_controller {
    uint64_t cap;     /* Controller Capabilities */
    uint32_t vs;      /* Version */
    uint32_t intms;   /* Interrupt Mask Set */
    uint32_t intmc;   /* Interrupt Mask Clear */
    uint32_t cc;      /* Controller Configuration */
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
#define NVME_VS_TER_MASK        NVME_BITS_MASK(0, 7)    /* Tertiary Version */
#define NVME_VS_MNR_SHIFT       8
#define NVME_VS_MNR_MASK        NVME_BITS_MASK(8, 15)   /* Minor Version */
#define NVME_VS_MJR_SHIFT       16
#define NVME_VS_MJR_MASK        NVME_BITS_MASK(16, 31)  /* Major Version */

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
