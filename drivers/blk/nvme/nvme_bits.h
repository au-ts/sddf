/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/*
 * Bitfield extraction helpers shared across NVMe headers.
 */

#include <sddf/util/util.h>

/* Inclusive bitfield mask helper. */
#define NVME_BITS_MASK(start, end) ((BIT(((end) - (start)) + 1U) - 1U) << (start))
