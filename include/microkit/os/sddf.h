/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <microkit.h>
#include <sel4/sel4.h>
#include <stdint.h>

typedef microkit_channel sddf_channel;

#define SDDF_NAME_LENGTH MICROKIT_PD_NAME_LENGTH

static inline char *sddf_get_pd_name()
{
    return microkit_name;
}

static inline void sddf_irq_ack(sddf_channel ch)
{
    microkit_irq_ack(ch);
}

static inline void sddf_deferred_irq_ack(sddf_channel ch)
{
    microkit_deferred_irq_ack(ch);
}

static inline void sddf_notify(sddf_channel ch)
{
    microkit_notify(ch);
}

static inline void sddf_deferred_notify(sddf_channel ch)
{
    microkit_deferred_notify(ch);
}

static inline unsigned int sddf_deferred_notify_curr()
{
    if (!microkit_have_signal) {
        return -1;
    }

    return microkit_signal_cap - BASE_OUTPUT_NOTIFICATION_CAP;
}

static inline microkit_msginfo sddf_ppcall(sddf_channel ch, microkit_msginfo msginfo)
{
    return microkit_ppcall(ch, msginfo);
}

static inline uint64_t sddf_get_mr(unsigned int n)
{
    return seL4_GetMR(n);
}

static inline void sddf_set_mr(unsigned int n, uint64_t val)
{
    seL4_SetMR(n, val);
}