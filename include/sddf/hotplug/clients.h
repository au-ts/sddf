/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <microkit.h>

/**
 * For inter-client communication & safe ejection.
 */

typedef struct hotplug_info {
    bool pending_eject;
} hotplug_info_t;

#define SDDF_HOTPLUG_CLIENT_READY_FOR_EJECT 1

// TODO: Doc Comments

static inline bool hotplug_is_pending_eject(hotplug_info_t *hotplug_info)
{
    return __atomic_load_n(&hotplug_info->pending_eject, __ATOMIC_ACQUIRE);
}

static inline void hotplug_set_pending_eject(hotplug_info_t *hotplug_info, microkit_channel client_ch,
                                             bool pending_eject)
{
    __atomic_store_n(&hotplug_info->pending_eject, pending_eject, __ATOMIC_RELEASE);
    if (pending_eject) {
        /* only for setting pending */
        microkit_notify(client_ch);
    }
}

static inline void hotplug_ready_for_eject(microkit_channel controller_ch)
{
    (void)microkit_ppcall(controller_ch, microkit_msginfo_new(SDDF_HOTPLUG_CLIENT_READY_FOR_EJECT, 0));
}
