/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <sddf/resources/common.h>

#define DEVICE_MAX_REGIONS 64
#define DEVICE_MAX_IRQS 64

typedef struct device_region_resource {
    region_resource_t region;
    uintptr_t io_addr;
} device_region_resource_t;

typedef struct device_irq_resource {
    uint8_t id;
} device_irq_resource_t;

typedef struct device_resources {
    uint8_t num_regions;
    uint8_t num_irqs;
    device_region_resource_t regions[DEVICE_MAX_REGIONS];
    device_irq_resource_t irqs[DEVICE_MAX_IRQS];
} device_resources_t;
