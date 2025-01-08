/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// OpenTitan I2C generic header

#pragma once

#include <cstdint>
#include <stdint.h>

typedef struct i2c_timing_params {
    uint8_t t_high_min;
    uint8_t t_low_min;
    uint8_t t_hd_sta_min;
    uint8_t t_su_sta_min;
    uint8_t t_hd_dat_min;
    uint8_t t_su_dat_min;
    uint8_t t_buf_min;
    uint8_t t_sto_min;
} i2c_timing_params_t;

#define KILO (1000)
#define MEGA (1000000)

/* I2C speed modes in Hz */
enum I2C_SPEED_MODE {
    I2C_SPEED_STD = (100 * KILO),
    I2C_SPEED_FAST = (400 * KILO),
    I2C_SPEED_FASTPLUS = (1 * MEGA)
};

#ifdef I2C_MODE_FAST
// Constants for Fast Mode in I2C spec (all in ns)
#define T_HIGH_MIN (600)    // SCL High period
#define T_LOW_MIN (1350)    // SCL Low period
#define T_HD_STA_MIN (600)  // Hold time (repeated) start condition
#define T_SU_STA_MIN (600)  // Set up time for a repeated start condition
#define T_HD_DAT_MIN (0)    // Data hold time (undefined for I2C! only needed for CBUS etc.)
#define T_SU_DAT_MIN (100)  // Data set up time
#define T_BUF_MIN (1300)    // Bus free time between start and stop
#define T_SU_STO_MIN (600)  // Set up time for a stop condition
                            // NOTE: the OpenTitan docs refer to just T_STO_min not this?
#endif
