/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <sddf/pmic/driver.h>

typedef struct bd71837_reg {
    const char *name;
    sddf_regulator_t reg;
    uint8_t i2c_reg_addr;
} bd71837_reg_t;


// IMPORTANT: this driver currently ONLY supports setting "run" mode parameters.
// We don't support setting idle or suspend mode parameters as these features
// cannot be harmoniously touched in LionsOS at the time of writing.
// TODO: sanity check the below, i am rushing and tired
#define BD71837_NUM_REGULATORS (15)
static bd71837_reg_t bd71837_regulator_table[BD71837_NUM_REGULATORS] = {
    /* BUCK1: VDD_SOC, 3.6A, 0.7-1.3V @ 10mV step (6-bit DVS) */
    {
        .name = "BUCK1",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 700000, .max_value = 1300000, .quantisation = 6 },
                .current = { .adjustable = false, .min_value = 3600000, .max_value = 3600000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 3600000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x0D,  /* BUCK1_VOLT_RUN */
    },
    /* BUCK2: VDD_ARM, 4.0A, 0.7-1.3V @ 10mV step (6-bit DVS) */
    {
        .name = "BUCK2",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 700000, .max_value = 1300000, .quantisation = 6 },
                .current = { .adjustable = false, .min_value = 4000000, .max_value = 4000000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 4000000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x10,  /* BUCK2_VOLT_RUN */
    },
    /* BUCK3: VDD_GPU, 2.1A, 0.7-1.3V @ 10mV step (6-bit DVS) */
    {
        .name = "BUCK3",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 700000, .max_value = 1300000, .quantisation = 6 },
                .current = { .adjustable = false, .min_value = 2100000, .max_value = 2100000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 2100000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x12,  /* BUCK3_VOLT_RUN */
    },
    /* BUCK4: VDD_VPU, 1.0A, 0.7-1.3V @ 10mV step (6-bit DVS) */
    {
        .name = "BUCK4",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 700000, .max_value = 1300000, .quantisation = 6 },
                .current = { .adjustable = false, .min_value = 1000000, .max_value = 1000000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 1000000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x13,  /* BUCK4_VOLT_RUN */
    },
    /* BUCK5: VDD_DRAM, 2.5A, 0.7-1.35V 8-step (3-bit, non-linear) */
    {
        .name = "BUCK5",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 700000, .max_value = 1350000, .quantisation = 3 },
                .current = { .adjustable = false, .min_value = 2500000, .max_value = 2500000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 2500000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x14,  /* BUCK5_VOLT */
    },
    /* BUCK6: NVCC_3P3, 3.0A, 3.0-3.3V @ 100mV step (2-bit, 4 values) */
    {
        .name = "BUCK6",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 3000000, .max_value = 3300000, .quantisation = 2 },
                .current = { .adjustable = false, .min_value = 3000000, .max_value = 3000000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 3000000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x15,  /* BUCK6_VOLT */
    },
    /* BUCK7: NVCC_1P8, 1.5A, 1.605-1.995V 8-step (3-bit, discrete steps) */
    {
        .name = "BUCK7",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 1605000, .max_value = 1995000, .quantisation = 3 },
                .current = { .adjustable = false, .min_value = 1500000, .max_value = 1500000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 1500000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x16,  /* BUCK7_VOLT */
    },
    /* BUCK8: NVCC_DRAM, 3.0A, 0.8-1.4V @ 10mV step (6-bit) */
    {
        .name = "BUCK8",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 800000, .max_value = 1400000, .quantisation = 6 },
                .current = { .adjustable = false, .min_value = 3000000, .max_value = 3000000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 3000000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x17,  /* BUCK8_VOLT */
    },
    /* LDO1: NVCC_SNVS, 10mA, 3.0-3.3V or 1.6-1.9V (2-bit + range sel) */
    {
        .name = "LDO1",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 1600000, .max_value = 3300000, .quantisation = 2 },
                .current = { .adjustable = false, .min_value = 10000, .max_value = 10000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 10000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x18,  /* LDO1_VOLT */
    },
    /* LDO2: VDD_SNVS, 10mA, 0.8V or 0.9V (1-bit) */
    {
        .name = "LDO2",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 800000, .max_value = 900000, .quantisation = 1 },
                .current = { .adjustable = false, .min_value = 10000, .max_value = 10000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 10000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x19,  /* LDO2_VOLT */
    },
    /* LDO3: VDDA_1P8/DRAM, 300mA, 1.8-3.3V @ 100mV step (4-bit) */
    {
        .name = "LDO3",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 1800000, .max_value = 3300000, .quantisation = 4 },
                .current = { .adjustable = false, .min_value = 300000, .max_value = 300000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 300000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x1A,  /* LDO3_VOLT */
    },
    /* LDO4: VDDA_0P9, 250mA, 0.9-1.8V @ 100mV step (4-bit) */
    {
        .name = "LDO4",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 900000, .max_value = 1800000, .quantisation = 4 },
                .current = { .adjustable = false, .min_value = 250000, .max_value = 250000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 250000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x1B,  /* LDO4_VOLT */
    },
    /* LDO5: PHY_1P8, 300mA, 1.8-3.3V @ 100mV step (4-bit) */
    {
        .name = "LDO5",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 1800000, .max_value = 3300000, .quantisation = 4 },
                .current = { .adjustable = false, .min_value = 300000, .max_value = 300000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 300000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x1C,  /* LDO5_VOLT */
    },
    /* LDO6: PHY_0P9, 300mA, 0.9-1.8V @ 100mV step (4-bit) */
    {
        .name = "LDO6",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 900000, .max_value = 1800000, .quantisation = 4 },
                .current = { .adjustable = false, .min_value = 300000, .max_value = 300000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 300000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x1D,  /* LDO6_VOLT */
    },
    /* LDO7: PHY_3P3, 150mA, 1.8-3.3V @ 100mV step (4-bit) */
    {
        .name = "LDO7",
        .reg = {
            .capabilities = {
                .voltage = { .adjustable = true, .min_value = 1800000, .max_value = 3300000, .quantisation = 4 },
                .current = { .adjustable = false, .min_value = 150000, .max_value = 150000, .quantisation = 0 },
                .toggleable = true,
            },
            .voltage_uv = 0,
            .current_ua = 150000,
            .enabled = true,
        },
        .i2c_reg_addr = 0x1E,  /* LDO7_VOLT */
    },
};

/* Registers specific to BD71837 */
enum {
	BD71837_REG_BUCK3_CTRL =	0x07,
	BD71837_REG_BUCK4_CTRL =	0x08,
	BD71837_REG_BUCK3_VOLT_RUN =	0x12,
	BD71837_REG_BUCK4_VOLT_RUN =	0x13,
	BD71837_REG_LDO7_VOLT =		0x1E,
};

/* Registers common for BD71837 and BD71847 */
enum {
	BD718XX_REG_REV =			0x00,
	BD718XX_REG_SWRESET =			0x01,
	BD718XX_REG_I2C_DEV =			0x02,
	BD718XX_REG_PWRCTRL0 =			0x03,
	BD718XX_REG_PWRCTRL1 =			0x04,
	BD718XX_REG_BUCK1_CTRL =		0x05,
	BD718XX_REG_BUCK2_CTRL =		0x06,
	BD718XX_REG_1ST_NODVS_BUCK_CTRL =	0x09,
	BD718XX_REG_2ND_NODVS_BUCK_CTRL =	0x0A,
	BD718XX_REG_3RD_NODVS_BUCK_CTRL =	0x0B,
	BD718XX_REG_4TH_NODVS_BUCK_CTRL =	0x0C,
	BD718XX_REG_BUCK1_VOLT_RUN =		0x0D,
	BD718XX_REG_BUCK1_VOLT_IDLE =		0x0E,
	BD718XX_REG_BUCK1_VOLT_SUSP =		0x0F,
	BD718XX_REG_BUCK2_VOLT_RUN =		0x10,
	BD718XX_REG_BUCK2_VOLT_IDLE =		0x11,
	BD718XX_REG_1ST_NODVS_BUCK_VOLT =	0x14,
	BD718XX_REG_2ND_NODVS_BUCK_VOLT =	0x15,
	BD718XX_REG_3RD_NODVS_BUCK_VOLT =	0x16,
	BD718XX_REG_4TH_NODVS_BUCK_VOLT =	0x17,
	BD718XX_REG_LDO1_VOLT =			0x18,
	BD718XX_REG_LDO2_VOLT =			0x19,
	BD718XX_REG_LDO3_VOLT =			0x1A,
	BD718XX_REG_LDO4_VOLT =			0x1B,
	BD718XX_REG_LDO5_VOLT =			0x1C,
	BD718XX_REG_LDO6_VOLT =			0x1D,
	BD718XX_REG_TRANS_COND0 =		0x1F,
	BD718XX_REG_TRANS_COND1 =		0x20,
	BD718XX_REG_VRFAULTEN =			0x21,
	BD718XX_REG_MVRFLTMASK0 =		0x22,
	BD718XX_REG_MVRFLTMASK1 =		0x23,
	BD718XX_REG_MVRFLTMASK2 =		0x24,
	BD718XX_REG_RCVCFG =			0x25,
	BD718XX_REG_RCVNUM =			0x26,
	BD718XX_REG_PWRONCONFIG0 =		0x27,
	BD718XX_REG_PWRONCONFIG1 =		0x28,
	BD718XX_REG_RESETSRC =			0x29,
	BD718XX_REG_MIRQ =			0x2A,
	BD718XX_REG_IRQ =			0x2B,
	BD718XX_REG_IN_MON =			0x2C,
	BD718XX_REG_POW_STATE =			0x2D,
	BD718XX_REG_OUT32K =			0x2E,
	BD718XX_REG_REGLOCK =			0x2F,
	BD718XX_REG_OTPVER =			0xFF,
	BD718XX_MAX_REGISTER =			0x100,
};

#define REGLOCK_PWRSEQ	0x1
#define REGLOCK_VREG	0x10

/* Generic BUCK control masks */
#define BD718XX_BUCK_SEL	0x02
#define BD718XX_BUCK_EN		0x01
#define BD718XX_BUCK_RUN_ON	0x04

/* Generic LDO masks */
#define BD718XX_LDO_SEL		0x80
#define BD718XX_LDO_EN		0x40

/* BD71837 BUCK ramp rate CTRL reg bits */
#define BUCK_RAMPRATE_MASK	0xC0
#define BUCK_RAMPRATE_10P00MV	0x0
#define BUCK_RAMPRATE_5P00MV	0x1
#define BUCK_RAMPRATE_2P50MV	0x2
#define BUCK_RAMPRATE_1P25MV	0x3

#define DVS_BUCK_RUN_MASK	0x3F
#define DVS_BUCK_SUSP_MASK	0x3F
#define DVS_BUCK_IDLE_MASK	0x3F

#define BD718XX_1ST_NODVS_BUCK_MASK	0x07
#define BD718XX_3RD_NODVS_BUCK_MASK	0x07
#define BD718XX_4TH_NODVS_BUCK_MASK	0x3F

#define BD71847_BUCK3_MASK		0x07
#define BD71847_BUCK3_RANGE_MASK	0xC0
#define BD71847_BUCK4_MASK		0x03
#define BD71847_BUCK4_RANGE_MASK	0x40

#define BD71837_BUCK5_MASK		0x07
#define BD71837_BUCK5_RANGE_MASK	0x80
#define BD71837_BUCK6_MASK		0x03

#define BD718XX_LDO1_MASK		0x03
#define BD718XX_LDO1_RANGE_MASK		0x20
#define BD718XX_LDO2_MASK		0x20
#define BD718XX_LDO3_MASK		0x0F
#define BD718XX_LDO4_MASK		0x0F
#define BD718XX_LDO6_MASK		0x0F

#define BD71837_LDO5_MASK		0x0F
#define BD71847_LDO5_MASK		0x0F
#define BD71847_LDO5_RANGE_MASK		0x20

#define BD71837_LDO7_MASK		0x0F

/* BD718XX Voltage monitoring masks */
#define BD718XX_BUCK1_VRMON80           0x1
#define BD718XX_BUCK1_VRMON130          0x2
#define BD718XX_BUCK2_VRMON80           0x4
#define BD718XX_BUCK2_VRMON130          0x8
#define BD718XX_1ST_NODVS_BUCK_VRMON80  0x1
#define BD718XX_1ST_NODVS_BUCK_VRMON130 0x2
#define BD718XX_2ND_NODVS_BUCK_VRMON80  0x4
#define BD718XX_2ND_NODVS_BUCK_VRMON130 0x8
#define BD718XX_3RD_NODVS_BUCK_VRMON80  0x10
#define BD718XX_3RD_NODVS_BUCK_VRMON130 0x20
#define BD718XX_4TH_NODVS_BUCK_VRMON80  0x40
#define BD718XX_4TH_NODVS_BUCK_VRMON130 0x80
#define BD718XX_LDO1_VRMON80            0x1
#define BD718XX_LDO2_VRMON80            0x2
#define BD718XX_LDO3_VRMON80            0x4
#define BD718XX_LDO4_VRMON80            0x8
#define BD718XX_LDO5_VRMON80            0x10
#define BD718XX_LDO6_VRMON80            0x20

/* BD71837 specific voltage monitoring masks */
#define BD71837_BUCK3_VRMON80           0x10
#define BD71837_BUCK3_VRMON130          0x20
#define BD71837_BUCK4_VRMON80           0x40
#define BD71837_BUCK4_VRMON130          0x80
#define BD71837_LDO7_VRMON80            0x40

/* BD718XX_REG_IRQ bits */
#define IRQ_SWRST		0x40
#define IRQ_PWRON_S		0x20
#define IRQ_PWRON_L		0x10
#define IRQ_PWRON		0x08
#define IRQ_WDOG		0x04
#define IRQ_ON_REQ		0x02
#define IRQ_STBY_REQ		0x01

/* ROHM BD718XX irqs */
enum {
	BD718XX_INT_STBY_REQ,
	BD718XX_INT_ON_REQ,
	BD718XX_INT_WDOG,
	BD718XX_INT_PWRBTN,
	BD718XX_INT_PWRBTN_L,
	BD718XX_INT_PWRBTN_S,
	BD718XX_INT_SWRST
};

/* ROHM BD718XX interrupt masks */
#define BD718XX_INT_SWRST_MASK		0x40
#define BD718XX_INT_PWRBTN_S_MASK	0x20
#define BD718XX_INT_PWRBTN_L_MASK	0x10
#define BD718XX_INT_PWRBTN_MASK		0x8
#define BD718XX_INT_WDOG_MASK		0x4
#define BD718XX_INT_ON_REQ_MASK		0x2
#define BD718XX_INT_STBY_REQ_MASK	0x1

/* Register write induced reset settings */

/*
 * Even though the bit zero is not SWRESET type we still want to write zero
 * to it when changing type. Bit zero is 'SWRESET' trigger bit and if we
 * write 1 to it we will trigger the action. So always write 0 to it when
 * changning SWRESET action - no matter what we read from it.
 */
#define BD718XX_SWRESET_TYPE_MASK	7
#define BD718XX_SWRESET_TYPE_DISABLED	0
#define BD718XX_SWRESET_TYPE_COLD	4
#define BD718XX_SWRESET_TYPE_WARM	6

#define BD718XX_SWRESET_RESET_MASK	1
#define BD718XX_SWRESET_RESET		1

