/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <stdint.h>

#define NET_BUFFER_SIZE 2048

/*
 * By default we assume that the hardware we are dealing with
 * cannot generate checksums on transmit. We use this macro
 * to know whether to calculate it in the IP stack.
 */
#if defined(CONFIG_PLAT_IMX8MM_EVK) || defined(CONFIG_PLAT_MAAXBOARD) || defined(CONFIG_PLAT_IMX8MP_EVK)               \
    || defined(CONFIG_PLAT_ODROIDC4) || defined(CONFIG_PLAT_STAR64) || defined(CONFIG_PLAT_HIFIVE_P550)                \
    || defined(CONFIG_PLAT_ODROIDC2)
#define NETWORK_HW_HAS_CHECKSUM
#endif
