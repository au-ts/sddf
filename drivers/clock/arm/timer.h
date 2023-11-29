/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>

/* Properties of a single timer device */
typedef struct {
    /* Timers are up counters or down counters.
     *
     * Up counters count up from 0, down counters count down from
     * a set value (set when a timeout is set up).
     *
     */
    uint32_t upcounter: 1;

    /* True if this timer supports setting timeouts at all */
    uint32_t timeouts: 1;

    /* what sort of timeouts does this timer support? */
    uint32_t absolute_timeouts: 1;
    uint32_t relative_timeouts: 1;
    uint32_t periodic_timeouts: 1;

    /* when does this timer roll over? This will be 0 for down-counters (max valueue 64) */
    uint32_t bit_width: 7;

    /* Number of unique irqs this timer issues */
    uint32_t irqs;
} timer_properties_t;
