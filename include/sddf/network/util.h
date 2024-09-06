/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/util/util.h>

#if BYTE_ORDER == BIG_ENDIAN
#define HTONS(x) ((uint16_t)(x))
#else
#define HTONS(x) ((uint16_t)((((x) & (uint16_t)0x00ffU) << 8) | (((x) & (uint16_t)0xff00U) >> 8)))
#endif

static void net_set_mac_addr(uint8_t *mac, uint64_t val)
{
    mac[0] = val >> 40 & 0xff;
    mac[1] = val >> 32 & 0xff;
    mac[2] = val >> 24 & 0xff;
    mac[3] = val >> 16 & 0xff;
    mac[4] = val >> 8 & 0xff;
    mac[5] = val & 0xff;
}