/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// OpenTitan I2C generic header. This file contains all OpenTitan specific definitions.

#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/config.h>
#include <sddf/resources/device.h>
#include <sddf/util/util.h>

typedef struct i2c_timing_params {
    uint32_t t_high_min;
    uint32_t t_low_min;
    uint32_t t_hd_sta_min;
    uint32_t t_su_sta_min;
    uint32_t t_hd_dat_min;
    uint32_t t_su_dat_min;
    uint32_t t_buf_min;
    uint32_t t_sto_min;
    uint32_t t_r;
    uint32_t t_f;
    uint32_t t_h;
    uint32_t t_l;
} i2c_timing_params_t;

#define KILO (1000)
#define MEGA (1000000)

/* I2C speed modes in Hz */
enum I2C_SPEED_MODE { I2C_SPEED_STD = (100 * KILO), I2C_SPEED_FAST = (400 * KILO), I2C_SPEED_FASTPLUS = (1 * MEGA) };

/* Fast mode settings */
#ifdef I2C_MODE_FAST
// Constants from Fast Mode in I2C spec (all in ns)
#define T_HIGH_MIN (600)    // SCL High period
#define T_LOW_MIN (1300)    // SCL Low period
#define T_HD_STA_MIN (600)  // Hold time (repeated) start condition
#define T_SU_STA_MIN (600)  // Set up time for a repeated start condition
#define T_HD_DAT_MIN (0)    // Data hold time (undefined for I2C! only needed for CBUS etc.)
#define T_SU_DAT_MIN (100)  // Data set up time
#define T_BUF_MIN (1300)    // Bus free time between start and stop
#define T_SU_STO_MIN (600) // Set up time for a stop condition
#define I2C_SCL_MAX_FREQ (I2C_SPEED_FAST)
#define I2C_SCL_MIN_T (2500) // Min period in nanoseconds (max frequency) -> 400kHz^-1 = 2500ns
#endif

