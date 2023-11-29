/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <stdint.h>
#include <assert.h>
#include "generic_timer.h"
#include "timer/frequency.h"

uint64_t generic_timer_get_time(generic_timer_t *timer)
{
    return freq_cycles_and_hz_to_ns(generic_timer_get_ticks(), timer->freq);
}

int generic_timer_get_init(generic_timer_t *timer)
{
    assert(timer != NULL);

    /* try to read the frequency */
    timer->freq = generic_timer_get_freq();

    /* fail init, we don't know what the frequency of the timer is */
    assert(timer->freq != 0);

    return 0;
}
