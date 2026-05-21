/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once
#include <sddf/util/util.h>

typedef struct imx8mq_tmu_regs {
    uint32_t tmr;               /* 0x00 - TMU mode register */
    uint32_t tsr;               /* 0x04 - TMU status register */
    uint32_t tmtmir;            /* 0x08 - TMU monitor temperature measurement interval register */
    uint32_t reserved0[5];        /* 0x0C-0x1F - Reserved */
    uint32_t tier;              /* 0x20 - TMU interrupt enable register */
    uint32_t tidr;              /* 0x24 - TMU interrupt detect register */
    uint32_t tiscr;             /* 0x28 - TMU interrupt site capture register */
    uint32_t ticscr;            /* 0x2C - TMU interrupt critical site capture register */
    uint32_t reserved1[4];      /* 0x30-0x3F - Reserved */
    uint32_t tmhtcr;            /* 0x40 - TMU monitor high temperature capture register */
    uint32_t tmltcr;            /* 0x44 - TMU monitor low temperature capture register */
    uint32_t reserved2[2];      /* 0x48-0x4F - Reserved */
    uint32_t tmhtitr;           /* 0x50 - TMU monitor high temperature immediate threshold register */
    uint32_t tmhtatr;           /* 0x54 - TMU monitor high temperature average threshold register */
    uint32_t tmhtactr;          /* 0x58 - TMU monitor high temperature average critical threshold register */
    uint32_t reserved3[9];      /* 0x5C-0x7F - Reserved */
    uint32_t ttcfgr;            /* 0x80 - TMU temperature configuration register */
    uint32_t tscfgr;            /* 0x84 - TMU sensor configuration register */
    uint32_t reserved4[30];     /* 0x88-0xFF - Reserved */
    uint32_t tritsr0;           /* 0x100 - TMU report immediate temperature site register 0 */
    uint32_t tratsr0;           /* 0x104 - TMU report average temperature site register 0 */
    uint32_t reserved5[2];      /* 0x108-0x10F - Reserved */
    uint32_t tritsr1;           /* 0x110 - TMU report immediate temperature site register 1 */
    uint32_t tratsr1;           /* 0x114 - TMU report average temperature site register 1 */
    uint32_t reserved6[2];      /* 0x118-0x11F - Reserved */
    uint32_t tritsr2;           /* 0x120 - TMU report immediate temperature site register 2 */
    uint32_t tratsr2;           /* 0x124 - TMU report average temperature site register 2 */
    uint32_t reserved7[996];    /* 0x128-0xF0F - Reserved */
    uint32_t ttr0cr;            /* 0xF10 - TMU temperature range 0 control register */
    uint32_t ttr1cr;            /* 0xF14 - TMU temperature range 1 control register */
    uint32_t ttr2cr;            /* 0xF18 - TMU temperature range 2 control register */
    uint32_t ttr3cr;            /* 0xF1C - TMU temperature range 3 control register */
} imx8mq_tmu_regs_t;

#define SENSOR_MAX_TEMP ((sddf_temp_celsius_t) 85)
#define SENSOR_MIN_TEMP ((sddf_temp_celsius_t) 0)
#define SENSOR_QUANTISATION (8)

/*
 * Register fields.
 * We define every bit field as follows:
 * Offset: number of bits the mask is shifted from the LSB.
 * Mask: mask of bits in the field, left-shifted by offset.
 * Bit: mask of exact bit (for single-bit fields).
 */

// TMR - TMU Mode Register
#define TMU_TMR_ME_BIT              (BIT(31))
#define TMU_TMR_MSITE_MASK          (0x7)
#define TMU_TMR_MSITE_OFFSET        (13)
#define TMU_TMR_MSITE_ARM_BIT       (BIT(13))
#define TMU_TMR_MSITE_GPU_BIT       (BIT(14))
#define TMU_TMR_MSITE_VPU_BIT       (BIT(15))
#define TMU_TMR_ALPF_MASK           (0x3)
#define TMU_TMR_ALPF_OFFSET         (26)

// TSR - TMU Status Register
#define TMU_TSR_MIE_BIT             (BIT(30))
#define TMU_TSR_ORL_BIT             (BIT(29))
#define TMU_TSR_ORH_BIT             (BIT(28))

// TMTMIR - TMU Monitor Temperature Measurement Interval Register
#define TMU_TMTMIR_TMI_MASK         (0xFFFF)

// TIER - TMU Interrupt Enable Register
#define TMU_TIER_ITTEIE_BIT         (BIT(31))
#define TMU_TIER_ATTEIE_BIT         (BIT(30))
#define TMU_TIER_ATCTEIE_BIT        (BIT(29))

// TIDR - TMU Interrupt Detect Register
#define TMU_TIDR_ITTE_BIT           (BIT(31))
#define TMU_TIDR_ATTE_BIT           (BIT(30))
#define TMU_TIDR_ATCTE_BIT          (BIT(29))

// TISCR - TMU Interrupt Site Capture Register
#define TMU_TISCR_ISITE_MASK        (0x7)
#define TMU_TISCR_ISITE_OFFSET      (29)
#define TMU_TISCR_ASITE_MASK        (0x7)
#define TMU_TISCR_ASITE_OFFSET      (13)

// TICSCR - TMU Interrupt Critical Site Capture Register
#define TMU_TICSCR_CASITE_MASK      (0x7)
#define TMU_TICSCR_CASITE_OFFSET    (13)

// TMHTCR - TMU Monitor High Temperature Capture Register
// Bit 31: V, Bits 11-0: TEMP
#define TMU_TMHTCR_V_MASK           (0x80000000)
#define TMU_TMHTCR_V_OFFSET         (31)
#define TMU_TMHTCR_V_BIT            (0x80000000)
#define TMU_TMHTCR_TEMP_MASK        (0x0FFF)
#define TMU_TMHTCR_TEMP_OFFSET      (0)

// TMLTCR - TMU Monitor Low Temperature Capture Register
// Bit 31: V, Bits 11-0: TEMP
#define TMU_TMLTCR_V_MASK           (0x80000000)
#define TMU_TMLTCR_V_OFFSET         (31)
#define TMU_TMLTCR_V_BIT            (0x80000000)
#define TMU_TMLTCR_TEMP_MASK        (0x0FFF)

// TMHTITR - TMU Monitor High Temperature Immediate Threshold Register
#define TMU_TMHTITR_EN_BIT          (BIT(31))
#define TMU_TMHTITR_TEMP_MASK       (0xff)

// TMHTATR - TMU Monitor High Temperature Average Threshold Register
#define TMU_TMHTATR_EN_BIT          (BIT(31))
#define TMU_TMHTATR_TEMP_MASK       (0xFF)

// TMHTACTR - TMU Monitor High Temperature Average Critical Threshold Register
#define TMU_TMHTACTR_EN_BIT         (BIT(31))
#define TMU_TMHTACTR_TEMP_MASK      (0xFF)

// TRITSRn - TMU Report Immediate Temperature Site Registers
#define TMU_TRITSR_V_BIT            (BIT(31))
#define TMU_TRITSR_TEMP_MASK        (0xff)

// TRATSRn - TMU Report Average Temperature Site Registers
#define TMU_TRATSR_V_BIT            (BIT(31))
#define TMU_TRATSR_TEMP_MASK        (0xFF)

