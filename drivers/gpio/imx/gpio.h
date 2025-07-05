/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

struct imx_gpio_regs {
    uint32_t dr;           /* 0x00 Data Register */
    uint32_t gdir;         /* 0x04 Direction Register */
    uint32_t psr;          /* 0x08 Pad Status Register */
    uint32_t icr1;         /* 0x0C Interrupt Config 1 */
    uint32_t icr2;         /* 0x10 Interrupt Config 2 */
    uint32_t imr;          /* 0x14 Interrupt Mask */
    uint32_t isr;          /* 0x18 Interrupt Status */
    uint32_t edge_sel;     /* 0x1C Edge Select */
};

typedef volatile struct imx_gpio_regs imx_gpio_regs_t;

#define ICR_LOW_LEVEL     0x0  /* 00 */
#define ICR_HIGH_LEVEL    0x1  /* 01 */
#define ICR_RISING_EDGE   0x2  /* 10 */
#define ICR_FALLING_EDGE  0x3  /* 11 */