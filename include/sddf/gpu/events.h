/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>

#define GPU_EVENTS_REGION_SIZE 0x1000

typedef struct gpu_events_t {
    bool display_info;
} gpu_events_t;

/**
 * Set a display info event.
 *
 * @param h queue handle containing events.
 */
static inline void gpu_events_set_display_info(gpu_events_t *events)
{
    __atomic_store_n(&events->display_info, true, __ATOMIC_RELEASE);
}

/**
 * Clear a display info event.
 *
 * @param h queue handle containing events.
 */
static inline void gpu_events_clear_display_info(gpu_events_t *events)
{
    __atomic_store_n(&events->display_info, false, __ATOMIC_RELEASE);
}

/**
 * Check if a display info event is set.
 *
 * @param h queue handle containing events.
 *
 * @return true if display info event is set, false otherwise.
 */
static inline bool gpu_events_check_display_info(gpu_events_t *events)
{
    return __atomic_load_n(&events->display_info, __ATOMIC_ACQUIRE);
}
