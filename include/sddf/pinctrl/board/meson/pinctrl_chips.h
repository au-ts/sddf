/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

// Each chip got a different number and names for its various pinmux controllers

typedef enum { PINCTRL_CHIP_AO, PINCTRL_CHIP_PERIPHERALS, PINCTRL_NUM_CHIPS } sddf_pinctrl_chip_idx_t;
