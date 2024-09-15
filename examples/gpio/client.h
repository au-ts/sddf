/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>

#define TIMER_CH (0)
#define GPIO_DRIVER_CH_1 (1)
#define GPIO_DRIVER_CH_2 (2)


bool delay_ms(size_t milliseconds);