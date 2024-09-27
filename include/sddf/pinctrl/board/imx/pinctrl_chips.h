/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

// Each chip got a different number and names for its various pinmux controllers

// On imx, we dont differentiate between the normal and GPR registers as they are
// contiguous in phys and virt memory.

typedef enum { PINCTRL_CHIP_IOMUXC, PINCTRL_NUM_CHIPS } sddf_pinctrl_chip_idx_t;
