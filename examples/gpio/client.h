/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>

#define CONTROL_FORWARD (1)
#define CONTROL_REVERSE (2)
#define CONTROL_NEUTRAL (3)

#define NS_IN_MS 1000000ULL

// Buffer Masks
#define RHR_MASK 0b111111111
#define UARTDR 0x000
#define UARTFR 0x018
#define UARTIMSC 0x038
#define UARTICR 0x044
#define PL011_UARTFR_TXFF (1 << 5)
#define PL011_UARTFR_RXFE (1 << 4)
#define REG_PTR(base, offset) ((volatile uint32_t *)((base) + (offset)))



