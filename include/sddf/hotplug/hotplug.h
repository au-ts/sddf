/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>


/**
 * TODO:
 * - Multiple devices.
 * - Is this really blk_storage_info_t?
 *
 */


#define SDDF_HOTPLUG_STATE_INSERTED    0
#define SDDF_HOTPLUG_STATE_EJECTING    1
#define SDDF_HOTPLUG_STATE_OK_TO_EJECT 2
#define SDDF_HOTPLUG_STATE_EJECTED     3

typedef struct hotplug_shared_device {
    uint8_t state;
} hotplug_shared_device_t;

static inline void sddf_hotplug_notify(microkit_channel channel, hotplug_shared_device_t *device, uint8_t new_state)
{
    __atomic_store_n(&device->state, new_state, __ATOMIC_RELEASE);
    microkit_notify(channel);
}
