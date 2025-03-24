/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

struct bench {
    uint64_t ccount;
    uint64_t prev;
    uint64_t ts;
};
