/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>

#pragma once

/* Shared functionality/definitions between pinctrl drivers and clients */

#define SDDF_CLK_ENABLE     0
#define SDDF_CLK_DISABLE    1
#define SDDF_CLK_GET_RATE   2
#define SDDF_CLK_SET_RATE   3

#define SDDF_CLK_PARAM_ID   0
#define SDDF_CLK_PARAM_RATE 1

struct clk_cfg {
    uint32_t clk_id;
    uint32_t frequency;
    uint32_t pclk_id;
};
