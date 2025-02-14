/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

// I2C header for the OpenTitan I2C IP block for the PULP Cheshire SoC in FAST mode (400KHz).
// Use this as a template for other device implementations using the same definitions.
// https://opentitan.org/book/hw/ip/i2c/doc/programmers_guide.html
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 01/2025

/* Register definitions */
#define I2C_BASE_ADDR        0x03003000

/* Timing properties for timing init algorithm */

// Input clock period (peripheral clocK)
#define T_CLK (20)      // SoC 50MHz clock is used directly for I2C(?) -> 50MHz^-1=20ns

// I2C speed mode
#define SPEED_MODE (I2C_SPEED_FAST)

// Expected bus rise time in ns
#define T_RISE (30)     // Value from table 11 in I2C spec UM10204 rev7

// Expected bus fall time in ns
#define T_FALL (12)     // t_f = 20ns * (Vdd / 5.5V) -> Vdd = 3.3V

// SCL period in ns
#define SCL_PERIOD (2500)   // 400KHz target -> (400KHz)^-1 = 2500nS

#define I2C_MODE_FAST   // Select fast mode
#define DUTY_100X 46    // 46% duty cycle * 100 for neater arithmetic

#define I2C_MAX_BUS_ADDRESS     (1 << 7)

/* FIFO config */
#define I2C_FMT_THRESHOLD       (1) // Only refill when FIFO is empty.
#define I2C_RX_THRESHOLD        (1) // Extract as soon as data is available.
