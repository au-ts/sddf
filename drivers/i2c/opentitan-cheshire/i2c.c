/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// I2C controller (master) driver for the OpenTitan I2C IP block (https://opentitan.org/book/hw/ip/i2c/)
// Currently uses the memory map for the Cheshire SoC targeting the Digilent Genesys2, but this should
// be trivial to adapt for other boards/SoCs. https://pulp-platform.github.io/cheshire/tg/xilinx/
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 01/2025

#include <microkit.h>
#include <sddf/i2c/queue.h>
#include "cheshire-i2c.h"   // Alternate devices should replace this include and substitute
                            // another header at compile time, preferably via the makefile.
#include "i2c.h"
#include <assert.h>

/* Clock value calculations */
#define MAX(a,b) ((a) > (b) ? (a) : (b))

// NOTE: the `0 +` before each division is to fool the preprocessor into consistent
// integer division.
i2c_timing_params_t timing_i2c = {
    .t_high_min = (MAX(((0 + T_HIGH_MIN)/(T_CLK)), 4)),
    .t_low_min = (MAX(((0 + T_HIGH_MIN)/(T_CLK)), 4)),
    .t_hd_dat_min = (MAX(((0 + T_HD_DAT_MIN) / (T_CLK)), 1)),
    .t_hd_sta_min = (((0 + T_HD_STA_MIN) / (T_CLK))),
    .t_su_sta_min = ((0 + T_SU_STA_MIN) / (T_CLK)),
    .t_buf_min = ((0 + T_BUF_MIN) / (T_CLK)),
    .t_sto_min = ((0 + T_SU_STO_MIN) / (T_CLK))
};

void init(void)
{
    // Perform initial set up - calculate and validate timing parameters

    // If any of the below conditions are not true, the device cannot initialise!
    assert(timing_i2c.t_hd_dat_min >= 1);
    assert(timing_i2c.t_hd_sta_min > timing_i2c.t_hd_dat_min);
    assert(timing_i2c.t_buf_min > timing_i2c.t_hd_dat_min);

    // Load timing parameters into registers

}
