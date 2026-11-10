/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>
#include <stdbool.h>
#include <stdint.h>

#define SDDF_MULTIKERNEL_MAX_CHANNELS 62

typedef struct {
    uint64_t vaddr; // MMIO write port to an AIA interrupt file.
    uint64_t identity;
} sddf_multikernel_peer_t;

typedef struct {
    uint64_t incoming;
    sddf_multikernel_peer_t channels[SDDF_MULTIKERNEL_MAX_CHANNELS];
} sddf_multikernel_config_t;

extern const sddf_multikernel_config_t *sddf_multikernel_config;

static inline bool sddf_send_ipi(unsigned ch)
{
    if (!sddf_multikernel_config || ch >= SDDF_MULTIKERNEL_MAX_CHANNELS) {
        return false;
    }
    const sddf_multikernel_peer_t *peer = &sddf_multikernel_config->channels[ch];
    if (!peer->identity) {
        return false;
    }
    asm volatile("fence rw, ow" ::: "memory");
    *(volatile uint32_t *)peer->vaddr = (uint32_t)peer->identity;
    return true;
}

// Required for IPIs unlike normal signals
static inline void sddf_multikernel_ack(unsigned ch)
{
    if (sddf_multikernel_config && ch < SDDF_MULTIKERNEL_MAX_CHANNELS
        && (sddf_multikernel_config->incoming & (UINT64_C(1) << ch))) {
        microkit_irq_ack(ch);
    }
}
