/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

typedef struct region_resource {
    void *vaddr;
    uint64_t size;
} region_resource_t;
