/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifndef CONF_TYPES_H_
#define CONF_TYPES_H_

#include <stdint.h>

struct clk_cfg {
    uint32_t clk_id;
    uint32_t frequency;
    uint32_t pclk_id;
};

#endif // CONF_TYPES_H_
