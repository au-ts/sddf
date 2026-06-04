/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>

#define UTILIZATION_PORT 1237

int setup_utilization_socket(void *benchmark_config);
