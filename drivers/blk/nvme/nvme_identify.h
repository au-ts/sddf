/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/*
 * Identify Controller and Identify Namespace response structures,
 * SGLS capability bits, LBA format parsing, and MDTS helpers.
 */

#include <stdint.h>
#include <stddef.h>
#include "nvme_bits.h"

/* Identify CNS values used by this driver. [NVMe-2.1 §5.1.13, Fig. 310] */
#define NVME_IDENTIFY_CNS_NAMESPACE  0x00U
#define NVME_IDENTIFY_CNS_CONTROLLER 0x01U

/*
 * Identify Controller (I/O Command Set Independent) response for CNS=01h.
 * Currently unused fields are modeled as reserved spans while preserving spec-defined offsets.
 * [NVMe-2.1 §5.1.13.2.1, Fig. 312]
 */
typedef struct nvme_identify_ctrl {
    uint16_t vid;    /* PCI Vendor ID */
    uint16_t ssvid;  /* PCI Subsystem Vendor ID */
    char sn[20];     /* Serial Number (ASCII, space-padded) */
    char mn[40];     /* Model Number (ASCII, space-padded) */
    char fr[8];      /* Firmware Revision (ASCII) */
    uint8_t _reserved0[77 - 72];
    uint8_t mdts;    /* Max transfer size exponent (0h means no limit; units based on CAP.MPSMIN) */
    uint8_t _reserved1[96 - 78];
    uint32_t ctratt; /* Controller Attributes (MEM bit 16 affects MDTS metadata accounting) */
    uint8_t _reserved2[512 - 100];
    uint8_t sqes;    /* MINSQES[3:0], MAXSQES[7:4] (required value is 6 => 64-byte SQE) */
    uint8_t cqes;    /* MINCQES[3:0], MAXCQES[7:4] (required value is 4 => 16-byte CQE) */
    uint8_t _reserved3[536 - 514];
    uint32_t sgls;   /* SGL Support */
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
#define NVME_IDENTIFY_ENTRY_SIZE_MIN_MASK  NVME_BITS_MASK(0, 3)
#define NVME_IDENTIFY_ENTRY_SIZE_MAX_SHIFT 4
#define NVME_IDENTIFY_ENTRY_SIZE_MAX_MASK  NVME_BITS_MASK(4, 7)

/* MDTS/size limits exclude metadata. [NVMe-2.1 Fig. 312] */
#define NVME_IDENTIFY_CTRATT_MEM BIT(16)

/* SGLS bits 1:0 transport encoding. [NVMe-2.1 Fig. 312] */
#define NVME_IDENTIFY_SGLS_TRANSPORT_MASK          NVME_BITS_MASK(0, 1)
#define NVME_IDENTIFY_SGLS_TRANSPORT_BYTE_ALIGNED  BIT(0)
#define NVME_IDENTIFY_SGLS_TRANSPORT_DWORD_ALIGNED BIT(1)

/* LBA Format entry layout. [NVM-CommandSet-1.1 Fig. 116] */
typedef struct nvme_lba_format {
    uint16_t ms;
    uint8_t lbads; /* 2^LBADS bytes; values < 9 are invalid. */
    uint8_t rp;    /* Bits 1:0 are RP; upper bits are reserved. */
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
#define NVME_IDENTIFY_FLBAS_FIDXL_MASK  NVME_BITS_MASK(0, 3)
#define NVME_IDENTIFY_FLBAS_FIDXU_SHIFT 5
#define NVME_IDENTIFY_FLBAS_FIDXU_MASK  NVME_BITS_MASK(5, 6)

static inline uint8_t nvme_identify_flbas_format_index(uint8_t flbas)
{
    uint8_t idx_low = (uint8_t)(flbas & NVME_IDENTIFY_FLBAS_FIDXL_MASK);
    uint8_t idx_high = (uint8_t)(((flbas & NVME_IDENTIFY_FLBAS_FIDXU_MASK) >> NVME_IDENTIFY_FLBAS_FIDXU_SHIFT) << 4);
    return (uint8_t)(idx_low | idx_high);
}
