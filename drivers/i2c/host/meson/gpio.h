/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// gpio.h
// Header for the ODROID C4's GPIO system. This should be replaced by a full
// generic GPIO driver in the sDDF in the future.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#include <sddf/util/util.h>

#pragma once
#define GPIO_OFFSET 1024

// Pinmux
#define GPIO_PINMUX_5 0xb5
#define GPIO_PM5_X17 BIT(4) | BIT(5) | BIT(6) | BIT(7)
#define GPIO_PM5_X18 BIT(8) | BIT(9) | BIT(10) | BIT(11)
#define GPIO_PM5_X_I2C 1

#define GPIO_PINMUX_E 0xbe
#define GPIO_PE_A14 BIT(27) | BIT(26) | BIT(25) | BIT(24)
#define GPIO_PE_A15 BIT(31) | BIT(30) | BIT(29) | BIT(28)
#define GPIO_PE_A_I2C 3

// Drive strengths
#define GPIO_DS_2B     0xd3 // M2
#define GPIO_DS_2B_X17 BIT(3) | BIT(2)
#define GPIO_DS_2B_X18 BIT(1) | BIT(0)  // Also used for X19, for some reason
#define GPIO_DS_2B_X17_SHIFT 2
#define GPIO_DS_2B_X18_SHIFT 4

#define GPIO_DS_5A     0xd4 // M3
#define GPIO_DS_5A_A14 BIT(28) | BIT(29)
#define GPIO_DS_5A_A15 BIT(30) | BIT(31)
#define GPIO_DS_5A_A14_SHIFT 28
#define GPIO_DS_5A_A15_SHIFT 30

#define DS_3MA 2

// Bias (pull up/down)
#define GPIO_BIAS_2     0x3c    // GPIO bank X
#define GPIO_BIAS_2_EN  0x4a
#define GPIO_BIAS_5     0x3f    // GPIO bank A
#define GPIO_BIAS_5_EN  0x4d
